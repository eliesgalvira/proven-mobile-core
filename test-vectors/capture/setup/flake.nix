{
  description = "Docker images for the 5G-spec-kernel golden capture: Open5GS 2.8.0 and UERANSIM 3.3.0, built from a pinned nixpkgs with dockerTools.";

  # Pinned nixpkgs revision that packages exactly open5gs 2.8.0 and ueransim 3.3.0.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/d357a2b54f0b6dc4aeb4e993190a52cf151b6f24";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        open5gs-image = pkgs.dockerTools.buildLayeredImage {
          name = "speck5g-open5gs";
          tag = "2.8.0";
          # coreutils + bash only so the container can be inspected; the daemons
          # are invoked directly by docker-compose, no shell wrapper.
          contents = [ pkgs.open5gs pkgs.coreutils pkgs.bashInteractive ];
          extraCommands = "mkdir -m 1777 tmp";
        };

        # Host-side tools for capture.py: tshark to filter the capture, Python with
        # `cryptography` for extract.py.
        extract-tools = pkgs.buildEnv {
          name = "speck5g-extract-tools";
          paths = [ pkgs.wireshark-cli (pkgs.python3.withPackages (p: [ p.cryptography ])) ];
        };

        # PacketRusher v2.0.0 runs the two gNBs and the UE of the handover capture.
        packetrusher = pkgs.callPackage ./packetrusher/package.nix { };

        packetrusher-image = pkgs.dockerTools.buildLayeredImage {
          name = "speck5g-packetrusher";
          tag = "2.0.0";
          # iproute2 adds the second gNB's address; iputils pings through the UE's tunnel.
          contents = [ self.packages.${system}.packetrusher pkgs.iproute2 pkgs.iputils pkgs.coreutils ];
          extraCommands = "mkdir -m 1777 tmp";
        };

        ueransim-image = pkgs.dockerTools.buildLayeredImage {
          name = "speck5g-ueransim";
          tag = "3.3.0";
          # nr-ue brings up its own TUN device but shells out to iproute2 for it;
          # iputils provides ping for the user-plane check.
          contents = [ pkgs.ueransim pkgs.iproute2 pkgs.iputils pkgs.coreutils pkgs.bashInteractive ];
          # nr-gnb / nr-ue keep a process table under /tmp/UERANSIM.proc-table, and
          # nr-ue appends its routing table to a writable /etc/iproute2/rt_tables.
          extraCommands = ''
            mkdir -m 1777 tmp
            mkdir -p etc/iproute2
            printf '255\tlocal\n254\tmain\n253\tdefault\n0\tunspec\n' > etc/iproute2/rt_tables
          '';
        };
      };
    };
}
