import KleinFour.LazyBlocks.Block00
import KleinFour.LazyBlocks.Block01
import KleinFour.LazyBlocks.Block02
import KleinFour.LazyBlocks.Block03
import KleinFour.LazyBlocks.Block04
import KleinFour.LazyBlocks.Block05
import KleinFour.LazyBlocks.Block06
import KleinFour.LazyBlocks.Block07
import KleinFour.LazyBlocks.Block08
import KleinFour.LazyBlocks.Block09
import KleinFour.LazyBlocks.Block10
import KleinFour.LazyBlocks.Block11
import KleinFour.LazyBlocks.Block12
import KleinFour.LazyBlocks.Block13
import KleinFour.LazyBlocks.Block14
import KleinFour.LazyBlocks.Block15
import KleinFour.LazyBlocks.Block16
import KleinFour.LazyBlocks.Block17
import KleinFour.LazyBlocks.Block18
import KleinFour.LazyBlocks.Block19
import KleinFour.LazyBlocks.Block20
import KleinFour.LazyBlocks.Block21
import KleinFour.LazyBlocks.Block22
import KleinFour.LazyBlocks.Block23
import KleinFour.LazyBlocks.Block24
import KleinFour.LazyBlocks.Block25
import KleinFour.LazyBlocks.Block26
import KleinFour.LazyBlocks.Block27
import KleinFour.LazyBlocks.Block28
import KleinFour.LazyBlocks.Block29
import KleinFour.LazyBlocks.Block30
import KleinFour.LazyBlocks.Block31
import KleinFour.LazyBlocks.Block32
import KleinFour.LazyBlocks.Block33
import KleinFour.LazyBlocks.Block34
import KleinFour.LazyBlocks.Block35
import KleinFour.LazyBlocks.Block36
import KleinFour.LazyBlocks.Block37
import KleinFour.LazyBlocks.Block38
import KleinFour.LazyBlocks.Block39
import KleinFour.LazyBlocks.Block40
import KleinFour.LazyBlocks.Block41
import KleinFour.LazyBlocks.Block42
import KleinFour.LazyBlocks.Block43
import KleinFour.LazyBlocks.Block44
import KleinFour.LazyBlocks.Block45
import KleinFour.LazyBlocks.Block46
import KleinFour.LazyBlocks.Block47
import KleinFour.LazyBlocks.Block48
import KleinFour.LazyBlocks.Block49
import KleinFour.LazyBlocks.Block50
import KleinFour.LazyBlocks.Block51
import KleinFour.LazyBlocks.Block52
import KleinFour.LazyBlocks.Block53
import KleinFour.LazyBlocks.Block54
import KleinFour.LazyBlocks.Block55
import KleinFour.LazyBlocks.Block56
import KleinFour.LazyBlocks.Block57
import KleinFour.LazyBlocks.Block58
import KleinFour.LazyBlocks.Block59
import KleinFour.LazyBlocks.Block60
import KleinFour.LazyBlocks.Block61
import KleinFour.LazyBlocks.Block62

namespace KleinFour.LazyCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem all_blocks (b : Fin 63) : CheckBlock b.val := by
  fin_cases b
  · exact block00
  · exact block01
  · exact block02
  · exact block03
  · exact block04
  · exact block05
  · exact block06
  · exact block07
  · exact block08
  · exact block09
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62

theorem block_index (i : Fin 4007) :
    blockIndex (i.val / 64) ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ = i := by
  apply Fin.ext
  simp only [blockIndex]
  omega

theorem all_boolean_edges (i : Fin 4007) (g : Fin 54) : booleanEdge i g = true := by
  have hb : i.val / 64 < 63 := by omega
  have h := (all_blocks ⟨i.val / 64, hb⟩).2 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ g
  simpa only [block_index] using h

theorem all_parent_indices (i : Fin 4007) : parentBoolean i = true ∧ indexBoolean i = true := by
  have hb : i.val / 64 < 63 := by omega
  have h := (all_blocks ⟨i.val / 64, hb⟩).1 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  simpa only [block_index] using h

end KleinFour.LazyCertificate
