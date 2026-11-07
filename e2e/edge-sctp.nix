# docs/spec/tickets/31-edge-sctp-coverage.md: the edge's tests on a kernel with
# SCTP loaded, where REQUIRE_SCTP=1 makes a test without SCTP fail.
{ edgeTests }:
{
  name = "speck5g-edge-sctp";

  nodes.machine = {
    boot.kernelModules = [ "sctp" ];
    virtualisation.memorySize = 512;
  };

  testScript = ''
    machine.wait_for_unit("systemd-modules-load.service")
    for test in machine.succeed("ls ${edgeTests}/bin").split():
        print(machine.succeed(f"REQUIRE_SCTP=1 ${edgeTests}/bin/{test} --nocapture 2>&1"))
  '';
}
