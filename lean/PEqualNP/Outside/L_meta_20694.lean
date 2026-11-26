import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20694

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_20694

theorem PEqualNP.Outside.L_meta_20694 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16125024 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20694.C, by simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20694.C], by decide, by decide +kernel⟩
