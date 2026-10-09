import KleinFour.LazyBounded

namespace KleinFour.LazyCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

theorem block56 : CheckBlock 56 := by
  unfold CheckBlock
  constructor <;> decide

end KleinFour.LazyCertificate
