import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Basic
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Graphical

noncomputable section
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration

/-- The signed manuscript edge total is nonnegative because it is half an actual
sum of bounded natural degrees. The conversion changes neither law nor window. -/
theorem graphInput_of_signed_total {V : Type*} [Fintype V]
    (N : ℕ) (m : ℤ) (p T : ℝ) (d : V → ℕ)
    (hcard : Fintype.card V = N) (hbounded : ∀ v, d v ≤ N-1)
    (htotal : ∑ v, (d v:ℤ) = 2*m)
    (hcount : |(m:ℝ)-p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N))
    (hdegree : ∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) :
    0 ≤ m ∧ (m.toNat:ℝ) = (m:ℝ) ∧ GraphInput N m.toNat p T d := by
  have hnonneg : (0:ℤ) ≤ ∑ v, (d v:ℤ) := Finset.sum_nonneg (fun v _ => Int.natCast_nonneg _)
  have hm : 0 ≤ m := by omega
  have hmc : (m.toNat:ℝ) = (m:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
  have ht : ∑ v, d v = 2*m.toNat := by
    have hh : ∑ v, (d v:ℤ) = 2*(m.toNat:ℤ) := by simpa only [Int.toNat_of_nonneg hm] using htotal
    exact_mod_cast hh
  exact ⟨hm,hmc,⟨hcard,hbounded,ht,by simpa only [hmc] using hcount,hdegree⟩⟩

/-- Signed bipartite size and edge totals are forced nonnegative by the actual
finite carrier and natural degree sums. Both degree tolerances retain p*N. -/
theorem bipartiteInput_of_signed_totals {L R : Type*} [Fintype L] [Fintype R]
    (N : ℕ) (ell m : ℤ) (p T : ℝ) (a : L → ℕ) (b : R → ℕ)
    (hcardL : (Fintype.card L:ℤ) = ell) (hcardR : Fintype.card R = N)
    (hsizeL : (N:ℝ)/T ≤ (ell:ℝ)) (hsizeU : (ell:ℝ) ≤ T*N)
    (hboundA : ∀ v, a v ≤ N) (hboundB : ∀ w, (b w:ℤ) ≤ ell)
    (htotalA : ∑ v, (a v:ℤ) = m) (htotalB : ∑ w, (b w:ℤ) = m)
    (hcount : |(m:ℝ)-p*(ell:ℝ)*N| ≤ T*N^2*p/Real.sqrt (p*N))
    (hdegreeA : ∀ v, |(a v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7))
    (hdegreeB : ∀ w, |(b w:ℝ)-p*(ell:ℝ)| ≤ (p*N)^((4:ℝ)/7)) :
    0 ≤ ell ∧ 0 ≤ m ∧ (ell.toNat:ℝ) = (ell:ℝ) ∧ (m.toNat:ℝ) = (m:ℝ) ∧
      BipartiteInput ell.toNat N m.toNat p T a b := by
  have he : 0 ≤ ell := hcardL ▸ Int.natCast_nonneg _
  have hm : 0 ≤ m := htotalA ▸ Finset.sum_nonneg (fun v _ => Int.natCast_nonneg _)
  have hec : (ell.toNat:ℝ) = (ell:ℝ) := by exact_mod_cast Int.toNat_of_nonneg he
  have hmc : (m.toNat:ℝ) = (m:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
  have hcL : Fintype.card L = ell.toNat := by omega
  have hb : ∀ w, b w ≤ ell.toNat := by intro w; have hh := hboundB w; omega
  have haT : ∑ v, a v = m.toNat := by
    have hh : ∑ v, (a v:ℤ) = (m.toNat:ℤ) := by simpa only [Int.toNat_of_nonneg hm] using htotalA
    exact_mod_cast hh
  have hbT : ∑ w, b w = m.toNat := by
    have hh : ∑ w, (b w:ℤ) = (m.toNat:ℤ) := by simpa only [Int.toNat_of_nonneg hm] using htotalB
    exact_mod_cast hh
  refine ⟨he,hm,hec,hmc,hcL,hcardR,?_,?_,hboundA,hb,haT,hbT,?_,hdegreeA,?_⟩
  · simpa only [hec] using hsizeL
  · simpa only [hec] using hsizeU
  · simpa only [hec,hmc] using hcount
  · simpa only [hec] using hdegreeB

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
