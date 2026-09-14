import MajorityDynamics.Idealized.CriticalDay.TiltApproximation
import MajorityDynamics.Idealized.CriticalDay.RelativeSizes
import MajorityDynamics.Idealized.CriticalDay.TemplateGain
import MajorityDynamics.Idealized.CriticalDay.RowLowerBounds

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

/-- All analytic outputs share one solved tilt. The gain is chosen before the
faithfulness exponent and before the auxiliary box bounds. -/
theorem analytic_assembly (θ T : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (n ell : ℕ) (hk : (n:ℝ)+1 = 1/(1-θ)) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ δ : ℝ, 0 < δ →
    ∃ R δ₁ φ : ℝ, 0 < R ∧ 0 < δ₁ ∧ 0 < φ ∧ φ < 1/2 ∧
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n+1) → ℤ, ∀ e : History (n+1) → History (n+1) → ℤ,
    FaithfulNumericalData N p T δ τ a n η e →
    ∃ σ : History (n+1) → Row (n+1),
      (∀ s t, |σ s t| ≤ R) ∧
      Local.Solves (naturalSizes η) (realEdges e) (fun s => RowLimits.rowTilt N p (σ s)) ∧
      (∀ s t, |(RowLimits.rowTilt N p (σ s) t:ℝ)-logitTilt N p (γ n s t) (ν n t)| ≤
        (p:ℝ)/Real.sqrt ((p:ℝ)*N)*(N:ℝ)^(-δ₁)) ∧
      (∀ s, φ ≤ Binomial.eventMass (Local.trials (naturalSizes η) s)
        (RowLimits.rowTilt N p (σ s)) (Local.historySupport (naturalSizes η) s)) ∧
      (∀ s b, φ ≤ RowLimits.binomialSplit N p (naturalSizes η) s b (σ s) ∧
        RowLimits.binomialSplit N p (naturalSizes η) s b (σ s) ≤ 1-φ) ∧
      (∀ s b, ζ*N ≤ sign b*(Local.templateSizes (naturalSizes η)
        (fun s => RowLimits.rowTilt N p (σ s)) (append s b)-(N:ℝ)*ν (n+1) (append s b))) := by
  obtain ⟨lo,hi,hlo,hlohi,hwindow⟩ := faithful_shift_window θ T hθlo hθhi hT n ell hk
  have hhi : 0 < hi := hlo.trans_le hlohi
  obtain ⟨ζ,hζ,hgain⟩ := template_gain_uniform n lo hlo
  refine ⟨ζ,hζ,?_⟩
  intro δ hδ
  obtain ⟨R,C,ρ,hR,hC,hρ,hγ,hsolve⟩ := solved_rows θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨φ,hφ,hφhi,e₁,he₁,hrow⟩ := row_lower_bounds n R hi hR.le hhi.le
  obtain ⟨e₂,he₂,hgain'⟩ := hgain R hi hR.le hhi.le hγ
  let b := min e₁ e₂
  have hb : 0 < b := lt_min he₁ he₂
  have hrate : 0 < responseRate θ 0 :=
    responseRate_pos hθlo hθhi (first_day_subcritical hθlo hθhi)
  have hdecay : Tendsto (fun N : ℕ => C*(N:ℝ)^(-ρ)+(N:ℝ)^(-responseRate θ 0)) atTop (nhds 0) := by
    have ha := ((tendsto_rpow_neg_atTop hρ).comp tendsto_natCast_atTop_atTop).const_mul C
    have hc := (tendsto_rpow_neg_atTop hrate).comp tendsto_natCast_atTop_atTop
    simpa using ha.add hc
  refine ⟨R,ρ/2,φ,hR,by positivity,hφ,hφhi,?_⟩
  filter_upwards [hsolve,hwindow δ hδ,
    relative_sizes θ T δ hθlo hθhi hT hδ n ell hk,
    tilt_approximation θ T R C ρ hθlo hθhi hT hR.le hC hρ n hγ,
    hdecay.eventually (eventually_le_nhds hb)] with N hs hw hz ht hsmall
  intro p hp a ha τ hτ hτT η e hf
  obtain ⟨σ,hσ,hclose,hq,hest⟩ := hs p hp a ha τ hτ hτT η e hf
  have hshift := hw p hp a ha τ hτ hτT η e hf
  have hsz := hz p hp a ha τ hτ hτT η e hf
  let E := C*(N:ℝ)^(-ρ)+(N:ℝ)^(-responseRate θ 0)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCE : C*(N:ℝ)^(-ρ) ≤ E := le_add_of_nonneg_right (by positivity)
  have hNE : (N:ℝ)^(-responseRate θ 0) ≤ E := le_add_of_nonneg_left (by positivity)
  have hE₁ : E ≤ e₁ := hsmall.trans (min_le_left _ _)
  have hE₂ : E ≤ e₂ := hsmall.trans (min_le_right _ _)
  have he' (s : History (n+1)) : RowLimits.Estimates N p (naturalSizes η) s (σ s)
      (RowLimits.shift N p (naturalSizes η)) 1 E :=
    Process.enlarge_estimates (hest s) (by simpa only [one_mul] using hCE)
  have hlower (s : History (n+1)) := hrow N p (naturalSizes η) s (σ s) E (hσ s)
    (by simpa only [abs_of_pos (hlo.trans_le hshift.1)] using hshift.2) hE hE₁ (he' s)
  refine ⟨σ,hσ,hq,ht p hp σ hσ hclose,fun s => (hlower s).1,fun s b => (hlower s).2 b,?_⟩
  apply hgain' N p (naturalSizes η) σ (RowLimits.shift N p (naturalSizes η)) E hE hE₂
    hshift.1 hshift.2 hσ
  · intro s t
    exact (hclose s t).trans hCE
  · intro s
    exact (hsz s).trans (mul_le_mul_of_nonneg_right hNE (Nat.cast_nonneg N))
  · intro s b
    simpa only [one_mul] using (he' s).split_probability b

end MajorityDynamics.Idealized.CriticalDay
