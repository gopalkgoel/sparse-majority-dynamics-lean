import MajorityDynamics.GraphProcess.EnumerationComparison.Applicability
import MajorityDynamics.GraphProcess.EnumerationComparison.BandScales

noncomputable section
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Universal BlockDecomposition EnumerationBounds
open Literature.DegreeEnumeration Probability.NeighborhoodBulk
variable {V : Type*} [Fintype V] {n : ℕ}

theorem prepared_internal_band (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {θ η T p : ℝ} (hη : 0 < η) (hηθ : η ≤ θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : Prepared y d T p)
    (hlo : T⁻¹*(Fintype.card V : ℝ)^(-θ) < p)
    (hhi : p < T*(Fintype.card V : ℝ)^(-η)) (s : History (n+1)) :
    GraphBandWindow θ η (4*T^4) (y.sizes s) (y.edge s s /2).toNat := by
  have hc := prepared_count_bounds y d hT h s s
  have he := internal_count_cast y s
  have hm : p*(Fintype.card V : ℝ)^2/(4*T^3) ≤
      (((y.edge s s/2).toNat : ℕ) : ℝ) := by
    have hi : p*(Fintype.card V : ℝ)^2/(2*T^3) =
        2*(p*(Fintype.card V : ℝ)^2/(4*T^3)) := by ring
    rw [hi] at hc
    linarith
  have hm' : (((y.edge s s/2).toNat : ℕ) : ℝ) ≤ 2*T*p*(Fintype.card V : ℝ)^2 := by
    have hz : (0:ℝ) ≤ (y.edge s s/2).toNat := by positivity
    linarith
  exact band_from_global hη hηθ hθhi hT h.card_pos (h.size_lower s)
    (by exact_mod_cast y.sizes_le_card s) hlo hhi hm hm'

theorem prepared_cross_band (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    {θ η T p : ℝ} (hη : 0 < η) (hηθ : η ≤ θ) (hθhi : θ < 1) (hT : 1 < T)
    (h : Prepared y d T p)
    (hlo : T⁻¹*(Fintype.card V : ℝ)^(-θ) < p)
    (hhi : p < T*(Fintype.card V : ℝ)^(-η)) (s t : History (n+1)) :
    BipartiteBandWindow θ η (4*T^4) (y.sizes t) (y.sizes s) (y.edge s t).toNat := by
  have hp := h.density_pos
  have hT0 : 0 < T := by linarith
  have hK : T ≤ 4*T^4 := by nlinarith [sq_nonneg (T^2-1), sq_nonneg (T-1)]
  have hsz : 0 ≤ (y.sizes t : ℝ) := by positivity
  have hc := prepared_count_bounds y d hT h s t
  refine ⟨?_, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_left hsz hT0 hK).trans
      ((div_le_div_of_nonneg_right (by exact_mod_cast y.sizes_le_card t) hT0.le).trans
        (h.size_lower s))
  · have hh := (div_le_iff₀ hT0).mp (h.size_lower t)
    exact (show (y.sizes s : ℝ) ≤ Fintype.card V by exact_mod_cast y.sizes_le_card s).trans
      (hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hK hsz]))
  · apply band_from_global hη hηθ hθhi hT h.card_pos (h.size_lower t)
      (by exact_mod_cast y.sizes_le_card t) hlo hhi
    · rw [edge_cast]
      have hi : p*(Fintype.card V : ℝ)^2/(2*T^3) =
          2*(p*(Fintype.card V : ℝ)^2/(4*T^3)) := by ring
      have hz : 0 ≤ p*(Fintype.card V : ℝ)^2/(4*T^3) := by positivity
      rw [hi] at hc
      linarith
    · rw [edge_cast]; exact hc.2

end MajorityDynamics.GraphProcess.EnumerationComparison
