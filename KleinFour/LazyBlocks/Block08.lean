import KleinFour.LazyBounded

namespace KleinFour.LazyCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

theorem block08 : CheckBlock 8 := by
  unfold CheckBlock
  constructor <;> decide

end KleinFour.LazyCertificate
