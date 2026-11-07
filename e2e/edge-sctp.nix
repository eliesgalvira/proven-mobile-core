# docs/spec/tickets/31-edge-sctp-coverage.md: the edge's tests on a kernel with
# SCTP loaded, where a test that prints SKIP fails the check.
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
        out = machine.succeed(f"${edgeTests}/bin/{test} --nocapture 2>&1")
        print(out)
        if "SKIP" in out:
            raise Exception(f"{test} skipped a test")
  '';
}
