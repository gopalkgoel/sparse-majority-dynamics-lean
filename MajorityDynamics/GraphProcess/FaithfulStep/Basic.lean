import MajorityDynamics.Idealized.PerturbedEvolution.Main
import MajorityDynamics.GraphProcess.LocalTransition.Basic
import MajorityDynamics.Idealized.Process.Finite

noncomputable section
namespace MajorityDynamics.GraphProcess.FaithfulStep
open Universal Idealized Idealized.LinearResponse Idealized.PerturbedTilt
open Idealized.PerturbedEvolution

variable {V : Type*} [Fintype V] {N n : ℕ}

/-- Changing the selected reference is exact on the recursively determined prefix. -/
theorem faithful_reference_iff {p T δ τ : ℝ} {a b : Process.Data}
    (h : a.state n = b.state n) (y : Local.CoarseData V n) :
    Faithful N p T δ τ a y ↔ Faithful N p T δ τ b y := by
  constructor
  · rintro ⟨hr, hs, he⟩
    exact ⟨hr, ⟨by simpa only [h] using hs, by simpa only [h] using he⟩⟩
  · rintro ⟨hr, hs, he⟩
    exact ⟨hr, ⟨by simpa only [h] using hs, by simpa only [h] using he⟩⟩

/-- Any two specifications, including different logarithmic exponents, have
exactly identical finite reference prefixes. -/
theorem reference_prefix {p : Binomial.Probability} {D ell ell' : ℕ}
    {a b : Process.Data} (ha : Process.Specification N p D ell a)
    (hb : Process.Specification N p D ell' b) : Process.AgreeThrough D a b :=
  Process.recursion_determined ha.toRecursion hb.toRecursion

/-- Literal local-success inclusion once the two uniform scale absorptions
are supplied. The closed uniform theorem below proves both absorptions. -/
theorem local_success_faithful {p C T₁ δ₁ δ₂ τ : ℝ} {a : Process.Data}
    (hN : 1 ≤ N) (hcard : Fintype.card V = N) (hp : 0 ≤ p)
    (hT : 0 ≤ T₁) (hδ : δ₂ ≤ δ₁)
    (hs : C * LocalTransition.sizeScale N ≤
      T₁ * sizeScale N p (n+1) * (N : ℝ)^(-δ₂))
    (he : C * LocalTransition.edgeScale N p ≤
      T₁ * betaScale N p (n+1) * (N : ℝ)^(-δ₂) * (N : ℝ)^2 * p)
    {y : Local.CoarseData V n} {q : Local.Tilt n}
    (ht : TemplateConclusion N p a y.sizes y.realEdges q τ T₁ δ₁)
    {z : Local.CoarseData V (n+1)} (hz : LocalTransition.LocalSuccess y q p C z) :
    Faithful N p (2*T₁) δ₂ τ a z := by
  have ht' := templateConclusion_mono hN hp hT le_rfl hδ ht
  refine ⟨hz.2.1, ?_, ?_⟩
  · intro u
    have hlu := hz.2.2.1 (parent u) (last u)
    rw [append_parent_last, hcard] at hlu
    have htri := abs_add_le
      ((z.sizes u : ℝ) - Local.templateSizes y.sizes q u)
      (Local.templateSizes y.sizes q u - ((a.state (n+1)).sizes u : ℝ) -
        τ * sizeScale N p (n+1) * ε (n+1) u)
    have htotal := add_le_add (hlu.trans hs) (ht'.sizes u)
    change |(z.sizes u : ℝ) - ((a.state (n+1)).sizes u : ℝ) -
      τ * sizeScale N p (n+1) * ε (n+1) u| ≤ _
    convert htri.trans htotal using 1 <;> congr 1 <;> ring
  · intro u v
    have hlu := hz.2.2.2 (parent u) (parent v) (last u) (last v)
    rw [append_parent_last, append_parent_last, hcard] at hlu
    have htri := abs_add_le
      (z.realEdges u v - Local.templateEdges y.sizes y.realEdges q u v)
      (Local.templateEdges y.sizes y.realEdges q u v - (a.state (n+1)).edges u v *
        (1 + τ * betaScale N p (n+1) * (ε (n+1) u / ν (n+1) u + ε (n+1) v / ν (n+1) v)))
    have htotal := add_le_add (hlu.trans he) (ht'.edges u v)
    change |z.realEdges u v - (a.state (n+1)).edges u v *
      (1 + τ * betaScale N p (n+1) * (ε (n+1) u / ν (n+1) u + ε (n+1) v / ν (n+1) v))| ≤ _
    convert htri.trans htotal using 1 <;> congr 1 <;> ring

end MajorityDynamics.GraphProcess.FaithfulStep
