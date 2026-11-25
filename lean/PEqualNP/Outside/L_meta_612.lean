import Mathlib
import PEqualNP.Defs

/-!
Reduction for L-meta-612 (shard 0 of 3): a cut of the statement
  |E| + tau <= size + 1, for a monotone AND/OR circuit of the edge function of a graph with
no 4-cycle, into two smaller statements about the library.

Split the gates of `C` into the OR gates and the gates that are not OR gates; the two sets are
disjoint and together are all `size` gates. Hypothesis one bounds the OR half (the half that
has to reach the edges: at least |E| - 1 of them); hypothesis two bounds the other half by a
vertex cover (at least tau of them). Adding the two bounds gives the step.
-/

namespace PEqualNP.Outside.LMeta612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- The OR gates of `C`, as wire indices below its output. -/
def orGates (C : Circuit) : Set ℕ :=
  {i | i < C.gates.length ∧ (gateAt C i).op = GateOp.or}

/-- The gates of `C` that are not OR gates, as wire indices below its output. -/
def nonOrGates (C : Circuit) : Set ℕ :=
  {i | i < C.gates.length ∧ (gateAt C i).op ≠ GateOp.or}

end PEqualNP.Outside.LMeta612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_612 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard ≤ (PEqualNP.Outside.LMeta612.orGates C).ncard + 1) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        S.card ≤ (PEqualNP.Outside.LMeta612.nonOrGates C).ncard) →
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro hOr hCover n t G C hedge h4 hcov hmin hmono heval
  have hsub : PEqualNP.Outside.LMeta612.orGates C ∪
      PEqualNP.Outside.LMeta612.nonOrGates C ⊆ Set.Iio C.gates.length := by
    intro i hi
    simp only [PEqualNP.Outside.LMeta612.orGates, PEqualNP.Outside.LMeta612.nonOrGates,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_Iio] at hi ⊢
    cases hi with
    | inl h => exact h.1
    | inr h => exact h.1
  have hdisj : Disjoint (PEqualNP.Outside.LMeta612.orGates C)
      (PEqualNP.Outside.LMeta612.nonOrGates C) := by
    rw [Set.disjoint_left]
    intro i h1 h2
    simp only [PEqualNP.Outside.LMeta612.orGates, PEqualNP.Outside.LMeta612.nonOrGates,
      Set.mem_ofPred_eq] at h1 h2
    exact h2.2 h1.2
  have hcard : (PEqualNP.Outside.LMeta612.orGates C).ncard +
      (PEqualNP.Outside.LMeta612.nonOrGates C).ncard ≤ C.gates.length := by
    have hf : (Set.Iio C.gates.length).Finite := Set.finite_Iio C.gates.length
    have ha : (PEqualNP.Outside.LMeta612.orGates C).Finite :=
      hf.subset (Set.subset_union_left.trans hsub)
    have hb : (PEqualNP.Outside.LMeta612.nonOrGates C).Finite :=
      hf.subset (Set.subset_union_right.trans hsub)
    calc _ = (PEqualNP.Outside.LMeta612.orGates C ∪
        PEqualNP.Outside.LMeta612.nonOrGates C).ncard :=
        (Set.ncard_union_eq hdisj ha hb).symm
      _ ≤ (Set.Iio C.gates.length).ncard := Set.ncard_le_ncard hsub hf
      _ = C.gates.length := Set.ncard_Iio_nat _
  obtain ⟨S, hS, hSc⟩ := hCover n G C h4 hmono heval
  have ht : t ≤ S.card := hmin S hS
  have h1 := hOr n G C h4 hmono heval
  have hsize : C.size = C.gates.length := rfl
  omega
