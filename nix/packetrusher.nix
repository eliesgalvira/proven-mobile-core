# PacketRusher v2.0.0 with this project's patch, used by the handover capture
# (test-vectors/capture/setup/flake.nix) and the end-to-end test (the root
# flake). The patch adds a control action that prepares an N2 handover and
# answers the Handover Command with a Handover Cancel.
{ buildGoModule, fetchFromGitHub }:
buildGoModule {
  pname = "packetrusher";
  version = "2.0.0-speck5g1";
  src = fetchFromGitHub {
    owner = "HewlettPackard";
    repo = "PacketRusher";
    rev = "6fef144296d4b1595e690a3d8e55c2a25407077b";
    hash = "sha256-DDVNlYBSGbaXu8RZ5/vaG+AdoPIxk77/yuhrlNlTEE0=";
  };
  patches = [ ./packetrusher-handover-cancel.patch ];
  vendorHash = "sha256-cwG0HhWD/lTcYIlDn5Fa+AgRuoU0ogXW3yBbLVTt0m0=";
  subPackages = [ "cmd" ];
  env.CGO_ENABLED = 0;
  ldflags = [ "-X main.version=v2.0.0+handover-cancel" ];
  # Upstream's tests open SCTP sockets and tunnels; the capture exercises the binary.
  doCheck = false;
  postInstall = "mv $out/bin/cmd $out/bin/packetrusher";
}
