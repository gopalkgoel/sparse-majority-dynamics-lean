import MajorityDynamics.GraphProcess.GoodArrayProbability.Main
import MajorityDynamics.GraphProcess.GoodArrays.Sparse
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Separate sparse-range versions; all original finite laws and predicates
are retained. Constants precede every varying finite datum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology
namespace MajorityDynamics.GraphProcess.GoodArrayProbability
open Universal
universe u

theorem uniform_coordinate_regime_sparse {θ T L : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hL : 1 ≤ L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p →
      ∀ v t,
      (q (y.part v) t : ℝ) ≤ 1/2 ∧
      L ≤ (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ∧
      (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ≤ 2*p*N ∧
      |(RowArray.naturalRows d v t : ℝ)-
        (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)| ≤
        coordinateConstant T * Real.sqrt
          ((Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)) := by
  obtain ⟨N₁, h₁⟩ := GoodArrays.uniform_regime_sparse n hθlo hθhi hT
  let X := max (4*T*L) ((2*T)^2)
  have hX : 0 < X := lt_of_lt_of_le (by positivity : 0 < (2*T)^2) (le_max_right _ _)
  obtain ⟨N₂, h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT hX
    (U := 1/4) (by norm_num) (M := 2*T) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  have hg := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y hsizes hcounts
  have hw := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  subst N
  exact finite_coordinate_regime y q hT hL hg hw.2.2.1 hw.2.2.2.2
    ((le_max_left _ _).trans hw.2.2.2.1) ((le_max_right _ _).trans hw.2.2.2.1)
    hsizes htilt d hd v t

theorem uniform_coordinate_lower_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p → ∀ v t,
        c/Real.sqrt (p*N) ≤ Binomial.Approximation.pointMass
          (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t)
          (q (y.part v) t) := by
  obtain ⟨c, hc, L, hL, hpoint⟩ := central_binomial_lower (coordinateConstant T)
    (coordinateConstant_pos hT).le
  obtain ⟨N₀, hN₀⟩ := uniform_coordinate_regime_sparse n hθlo hθhi hT hL
  refine ⟨c/2, by positivity, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  obtain ⟨hq, hmean, hupper, hwindow⟩ :=
    hN₀ N hN V hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  let μ : ℝ := (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)
  have hμ : 0 < μ := by dsimp [μ]; linarith
  have hx : 0 < p*N := by dsimp [μ] at hμ; nlinarith
  have hs : Real.sqrt μ ≤ 2*Real.sqrt (p*N) := by
    have := Real.sq_sqrt hμ.le
    have := Real.sq_sqrt hx.le
    have := Real.sqrt_nonneg μ
    have := Real.sqrt_nonneg (p*N)
    change μ ≤ 2*p*N at hupper
    nlinarith
  calc
    (c/2)/Real.sqrt (p*N) = c/(2*Real.sqrt (p*N)) := by ring
    _ ≤ c/Real.sqrt μ := div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.2 hμ) hs
    _ ≤ _ := hpoint _ _ _ hq hmean hwindow

/-- The complete point estimate, for both the original row law and its exact-count
conditioning. Constants precede all varying data; the exponent is literal real division. -/
theorem uniform_point_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p →
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (RowArray.law y.part q).real {d} ∧
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} := by
  obtain ⟨c, hc, N₁, h₁⟩ := uniform_coordinate_lower_sparse n hθlo hθhi hT
  obtain ⟨N₂, h₂⟩ := GoodArrays.uniform_regime_sparse n hθlo hθhi hT
  let C := (|Real.log c|+1)*(2^(n+1) : ℕ)
  refine ⟨C, by dsimp [C]; positivity, max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd
  have hreg := h₂ N ((le_max_right _ _).trans hN) V hcard p hlo hhi y hsizes hcounts
  have hx : 0 < p*N := by simpa only [hcard] using mul_pos hreg.density_pos hreg.card_pos
  have hprod := row_atom_of_coordinate_bound y q d
    (div_nonneg hc.le (Real.sqrt_nonneg _))
    (h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hsizes hcounts htilt d hd)
  rw [hcard] at hprod
  have hb := (coordinate_power_bound n N hc hx).trans hprod
  exact ⟨hb, hb.trans (row_atom_le_conditioned y q d ((GoodArrays.mem_E0 y T p d).mp hd).1)⟩

theorem uniform_probability_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Real.exp (-C*N) ≤ (RowArray.law y.part q).real (GoodArrays.E0 y T p) ∧
      Real.exp (-C*N) ≤
        (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real
          (GoodArrays.E0 y T p) ∧
      (GoodArrays.Separated y T p →
        Real.exp (-C*N) ≤ (RowArray.law y.part q).real
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge ∩
            {d | RowArray.Regular p d} ∩ {d | RowArray.Gamma y.part y.edge 1 p d})) := by
  obtain ⟨Cpoint, hCpoint, Npoint, hpoint⟩ := uniform_point_sparse n hθlo hθhi hT
  obtain ⟨Ccount, hCcount, Ncount, hcount⟩ := GoodArrays.uniform_cardinality_sparse n hθlo hθhi hT
  obtain ⟨Nreg, hreg⟩ := GoodArrays.uniform_regime_sparse n hθlo hθhi hT
  refine ⟨Ccount+Cpoint, add_pos hCcount hCpoint, max Npoint (max Ncount Nreg), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt
  have hNp : Npoint ≤ N := (le_max_left _ _).trans hN
  have hNc : Ncount ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNr : Nreg ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hr := hreg N hNr V hcard p hlo hhi y hsizes hcounts
  have hx : 0 < p*N := by
    simpa only [hcard] using mul_pos hr.density_pos hr.card_pos
  let b : ℝ := Real.exp (-Cpoint*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2))
  have hb : 0 ≤ b := mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hx _).le
  have hpoints : ∀ d ∈ GoodArrays.E0 y T p, b ≤ (RowArray.law y.part q).real {d} := by
    intro d hd
    exact (hpoint N hNp V hcard p hlo hhi y q hsizes hcounts htilt d hd).1
  have hcardinal := hcount N hNc V hcard p hlo hhi y hsizes hcounts
  have htotal : Real.exp (-(Ccount+Cpoint)*N) ≤
      (RowArray.law y.part q).real (GoodArrays.E0 y T p) := by
    calc
      _ = (Real.exp (-Ccount*N)*(p*N)^(((2^(n+1)*N : ℕ) : ℝ)/2))*b :=
        (count_point_cancellation hx N (2^(n+1)*N)).symm
      _ ≤ ((GoodArrays.E0 y T p).card : ℝ)*b :=
        mul_le_mul_of_nonneg_right hcardinal hb
      _ ≤ _ := card_mul_point_le_event y q T p b hpoints
  refine ⟨htotal, htotal.trans (E0_le_conditioned y q T p), ?_⟩
  intro hsep
  apply htotal.trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro d hd
  exact ⟨⟨⟨GoodArrays.e0_history hT hr hsep hd,
    ((GoodArrays.mem_E0 y T p d).mp hd).1⟩,
    GoodArrays.e0_regular hT hr hd⟩, GoodArrays.e0_gamma_one hT hr hd⟩

end MajorityDynamics.GraphProcess.GoodArrayProbability
