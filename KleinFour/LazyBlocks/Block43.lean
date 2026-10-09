import KleinFour.LazyBounded

namespace KleinFour.LazyCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

theorem block43 : CheckBlock 43 := by
  unfold CheckBlock
  constructor <;> decide

end KleinFour.LazyCertificate
