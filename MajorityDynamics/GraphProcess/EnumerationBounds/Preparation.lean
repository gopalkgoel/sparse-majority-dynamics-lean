import MajorityDynamics.GraphProcess.EnumerationBounds.Basic
import MajorityDynamics.GraphProcess.EnumerationBounds.Numerics
import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics

/-! Discharge the numerical regime from the manuscript's original hypotheses. -/
noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationBounds
open Universal
universe u

theorem entry_from_centers {v a b x T : ℝ}
    (hreg : |v-b| ≤ x^(4/7:ℝ))
    (havg : |a-b| ≤ T^2*Real.sqrt x)
    (hpay : T^2*Real.sqrt x ≤ x^(4/7:ℝ)) :
    |v-a| ≤ 2*x^(4/7:ℝ) := by
  have htri : |v-a| ≤ |v-b|+|a-b| := by
    calc
      |v-a| = |(v-b)+(b-a)| := by congr 1; ring
      _ ≤ |v-b|+|b-a| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm b a]
  linarith

/-- All required finite preparation inequalities on the actual array. -/
theorem finite_preparation {V : Type u} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) {T p : ℝ}
    (hT : 1 < T) (hN : 0 < (Fintype.card V : ℝ)) (hp : 0 < p)
    (hNsize : 2*T ≤ (Fintype.card V : ℝ))
    (hx : 1 ≤ p*Fintype.card V) (hxT : 4*T^6 ≤ p*Fintype.card V)
    (hpsmall : p ≤ 1/(8*T^2))
    (hdev : T^2*Real.sqrt (p*Fintype.card V) ≤ (p*Fintype.card V)^(4/7:ℝ))
    (hentry : 2*(p*Fintype.card V)^(4/7:ℝ) ≤
      (p*Fintype.card V/(2*T^2))^(7/12:ℝ))
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (hcounts : ∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(Fintype.card V : ℝ)^2*p/Real.sqrt (p*Fintype.card V))
    (hreg : RowArray.Regular p d) : Prepared y d T p := by
  have hT0 : 0 < T := by linarith
  have hup : ∀ s, (y.sizes s : ℝ) ≤ Fintype.card V := by
    intro s
    exact_mod_cast y.sizes_le_card s
  have hpair := fun s t => pair_estimates hN hT hp hxT
    (hsizes s) (hsizes t) (hup s) (hup t) (hcounts s t)
  have hsize := fun s => size_estimates hT hNsize (hsizes s)
  have hint := fun s => internal_estimates hN hT hp hxT hNsize
    (hsizes s) (hup s) (hcounts s s)
  have he : ∀ s t v, v ∈ History.block y.part s →
      |(RowArray.values d v t : ℝ)-avg y s t| ≤
        2*(p*Fintype.card V)^(4/7:ℝ) := by
    intro s t v _hv
    exact entry_from_centers (hreg v t) (hpair s t).2.2.1 hdev
  refine ⟨hN, hp, hx, fun s => (hsize s).1, hsizes,
    fun s => (hsize s).2, fun s t => (hpair s t).1,
    fun s t => (hpair s t).2.1, fun s t => (hpair s t).2.2.1,
    fun s => (hint s).1, fun s => (hint s).2,
    fun s t => (hpair s t).2.2.2.1, fun s t => (hpair s t).2.2.2.2,
    ?_, he, ?_⟩
  · have hh := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hpsmall
    nlinarith
  · intro s t v hv
    apply (he s t v hv).trans (hentry.trans ?_)
    exact Real.rpow_le_rpow (by positivity) (hpair s t).1 (by norm_num)

/-- One threshold, before every varying graph carrier and array, supplies all
numerical preparation; no history, attainability or graphicality is assumed. -/
theorem uniform_preparation {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.Regular p d → Prepared y d T p := by
  have hT0 : 0 < T := by linarith
  obtain ⟨X, _hX0, hX⟩ := eventually_deviation_regime hT
  obtain ⟨N₀, hN₀⟩ := eventually_window hθlo hθhi hT
    (L := max 1 (max (4*T^6) X)) (U := 1/(8*T^2)) (M := 2*T)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hNN V inst hcard n p hlo hhi y d hsizes hcounts hreg
  obtain ⟨hN, hp, hNsize, hx, hsmall⟩ := hN₀ N hNN p hlo hhi
  have hx1 : 1 ≤ p*N := (le_max_left _ _).trans hx
  have hxT : 4*T^6 ≤ p*N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxX : X ≤ p*N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  obtain ⟨hdev, hentry⟩ := hX (p*N) hxX
  subst N
  exact finite_preparation y d hT hN hp hNsize hx1 hxT hsmall hdev hentry
    hsizes hcounts hreg

end MajorityDynamics.GraphProcess.EnumerationBounds
