import Base
import ./vec.bend as V
import ../vectors/capture-vectors.bend as Capture
import ../vectors/capture-handover.bend as Handover
import ../vectors/hand-ngap-handover.bend as Hand

# The messages of the vector files with NGAP in them, in the order
# tools/ngap-gen/oracle.py reads them: the two captures, then the hand-made
# handover messages.
def Ngap.captured() -> List<&2, V.Vec>:
  List.append(&2, V.Vec, V.Vec.items(V.Vec.field(Capture.data(), "messages")), V.Vec.items(V.Vec.field(Handover.data(), "messages")))

def Ngap.vectors() -> List<&2, V.Vec>:
  List.append(&2, V.Vec, Ngap.captured(), V.Vec.items(V.Vec.field(Hand.data(), "messages")))
