{
  description = "5G spec kernel: the Bend 2 kernel, the Rust edge, and the end-to-end test against UERANSIM, PacketRusher and eUPF";

  # The revision the golden capture used: it packages UERANSIM 3.3.0 and Go 1.26.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/d357a2b54f0b6dc4aeb4e993190a52cf151b6f24";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      inherit (pkgs) lib;

      # The release binary is Bun with its payload in an ELF section; only the
      # interpreter is patched, and bend2/ must stay beside bin/ where it looks for it.
      bend = pkgs.stdenv.mkDerivation (finalAttrs: {
        pname = "bend";
        version = "2.0.39";
        src = pkgs.fetchurl {
          url = "https://github.com/bendlang/bend/releases/download/v${finalAttrs.version}/bend-${finalAttrs.version}-linux-x64.tar.gz";
          hash = "sha256-bPRi/Y9wsJSklQ67cJqcT/2PHRGJ2c7fH9Y81dBBx6s=";
        };
        dontStrip = true;
        dontPatchELF = true;
        installPhase = ''
          mkdir -p $out
          cp -r bin bend2 guide $out/
          patchelf --set-interpreter ${pkgs.stdenv.cc.bintools.dynamicLinker} $out/bin/bend
        '';
      });

      # `bend --verdict` builds its kernel with exactly this Lean (nixpkgs has a newer one).
      lean = pkgs.stdenv.mkDerivation (finalAttrs: {
        pname = "lean";
        version = "4.34.0";
        src = pkgs.fetchurl {
          url = "https://github.com/leanprover/lean4/releases/download/v${finalAttrs.version}/lean-${finalAttrs.version}-linux.tar.zst";
          hash = "sha256-yqqYNWCYyF3A/LvSjh7GbznrZVGCmXK3Uv8g4ShrZGs=";
        };
        nativeBuildInputs = [ pkgs.zstd pkgs.autoPatchelfHook ];
        buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
        dontStrip = true;
        installPhase = ''
          mkdir -p $out
          cp -r . $out/
        '';
      });

      kernel = pkgs.stdenv.mkDerivation {
        pname = "speck5g-kernel";
        version = "0.1.0";
        src = lib.fileset.toSource { root = ./.; fileset = lib.fileset.difference ./kernel ./kernel/tests; };
        nativeBuildInputs = [ bend pkgs.clang ];
        env.BEND_NO_TELEMETRY = "1";
        buildPhase = ''
          HOME=$TMPDIR bend kernel/main.bend -o kernel-bin
        '';
        installPhase = ''
          install -Dm755 kernel-bin $out/bin/kernel
        '';
      };

      edge = pkgs.rustPlatform.buildRustPackage {
        pname = "speck5g-edge";
        version = "0.1.0";
        src = lib.fileset.toSource {
          root = ./.;
          fileset = lib.fileset.unions [ ./edge ./test-vectors/frames.json ];
        };
        buildAndTestSubdir = "edge";
        cargoRoot = "edge";
        cargoLock.lockFile = ./edge/Cargo.lock;
      };

      # The edge's test binaries, which the edge-sctp check runs where SCTP is loaded.
      edgeTests = edge.overrideAttrs (old: {
        pname = "speck5g-edge-tests";
        nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.jq ];
        buildPhase = ''
          cd edge
          cargo test --offline --no-run --message-format=json | jq -r 'select(.profile.test) | .executable' > $NIX_BUILD_TOP/test-binaries
        '';
        doCheck = false;
        installPhase = ''
          install -Dt $out/bin $(cat $NIX_BUILD_TOP/test-binaries)
        '';
      });

      packetrusher = pkgs.callPackage ./nix/packetrusher.nix { };

      eupf = pkgs.buildGoModule (finalAttrs: {
        pname = "eupf";
        version = "0.7.2";
        src = pkgs.fetchFromGitHub {
          owner = "edgecomllc";
          repo = "eupf";
          rev = "v${finalAttrs.version}";
          hash = "sha256-GBHsRH3fW3VOxTMULreMrLt+OW5oFD1QZ23yMM5qchs=";
        };
        # bpf2go runs through `go run`, so it needs the full module cache, not a vendor tree.
        proxyVendor = true;
        vendorHash = "sha256-IZaJ3dxeh3fc/fN8aMxeFgmMcdQdaslIXGp7Q5hwe/Q=";
        overrideModAttrs = _: { preBuild = ""; };
        nativeBuildInputs = [ pkgs.clang pkgs.llvm pkgs.go-swag ];
        buildInputs = [ pkgs.libbpf ];
        # For `-target bpf`: the cc wrapper's hardening flags are invalid, and glibc's
        # headers need the 32-bit stubs that upstream gets from gcc-multilib.
        hardeningDisable = [ "all" ];
        env.NIX_CFLAGS_COMPILE = "-isystem ${pkgs.glibc_multi.dev}/include";
        env.CGO_ENABLED = "0";
        preBuild = ''
          go generate ./cmd/...
        '';
        subPackages = [ "cmd" ];
        postInstall = ''
          mv $out/bin/cmd $out/bin/eupf
        '';
      });
    in
    {
      packages.${system} = { inherit bend lean kernel edge eupf packetrusher; };
      # The NGAP generator needs pycrate's ASN.1 compiler only; cryptomobile (unfree) and pysctp are dropped.
      devShells.${system}.default = pkgs.mkShell {
        # pkgs.clang goes before lean, whose release bundles a clang without system headers.
        packages = [ bend pkgs.clang lean pkgs.cargo pkgs.rustc pkgs.nushell (pkgs.python3.withPackages (p: [ (p.pycrate.overridePythonAttrs (o: { dependencies = [ p.lxml ]; })) ])) ];
        BEND_NO_TELEMETRY = "1";
      };
      checks.${system} = {
        e2e = pkgs.testers.runNixOSTest (import ./e2e/test.nix { inherit kernel edge eupf packetrusher; });
        edge-sctp = pkgs.testers.runNixOSTest (import ./e2e/edge-sctp.nix { inherit edgeTests; });
      };
    };
}
