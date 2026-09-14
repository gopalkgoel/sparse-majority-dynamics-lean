import MajorityDynamics.GraphProcess.FineKernel.Main
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.CoarseKernel
open FineState History Local
variable {V : Type*} [Fintype V] {n : ℕ}

@[ext] theorem coarse_ext {x y : CoarseData V n}
    (hp : x.part = y.part) (he : x.edge = y.edge) (hr : x.reg = y.reg) : x = y := by
  cases x; cases y; cases hp; cases he; cases hr; rfl

theorem edge_bound (y : CoarseData V n) (s t : Universal.History (n+1)) :
    y.edge s t ≤ (Fintype.card V : ℤ) ^ 2 := by
  have hs : (partSizes y.part s : ℤ) ≤ Fintype.card V := by exact_mod_cast y.sizes_le_card s
  have ht : (partSizes y.part t : ℤ) ≤ Fintype.card V := by exact_mod_cast y.sizes_le_card t
  have h := y.edge_upper s t
  have hsub : (partSizes y.part t : ℤ) - (if s = t then 1 else 0) ≤ partSizes y.part t := by
    split_ifs <;> omega
  have hh := mul_le_mul_of_nonneg_left hsub (show (0:ℤ) ≤ partSizes y.part s by positivity)
  have hm := mul_le_mul hs ht (show (0:ℤ) ≤ partSizes y.part t by positivity)
    (show (0:ℤ) ≤ Fintype.card V by positivity)
  nlinarith

def encode (y : CoarseData V n) :
    (V → Universal.History (n+1)) ×
      (Universal.History (n+1) → Universal.History (n+1) → Fin ((Fintype.card V)^2+1)) × Bool :=
  (y.part, fun s t => ⟨(y.edge s t).toNat, by
    have h := edge_bound y s t
    have hn := y.edge_nonneg s t
    have hc : ((y.edge s t).toNat : ℤ) = y.edge s t := Int.toNat_of_nonneg hn
    have hN : (y.edge s t).toNat ≤ (Fintype.card V)^2 := by
      rw [← hc] at h
      exact_mod_cast h
    omega⟩, y.reg)

theorem encode_injective : Function.Injective (encode (V:=V) (n:=n)) := by
  intro x y h
  apply coarse_ext (congrArg Prod.fst h) _ (congrArg (fun z => z.2.2) h)
  funext s t
  have he := congrArg (fun z => ((z.2.1 s t : Fin ((Fintype.card V)^2+1)) : ℕ)) h
  change (x.edge s t).toNat = (y.edge s t).toNat at he
  have hx := Int.toNat_of_nonneg (x.edge_nonneg s t)
  have hy := Int.toNat_of_nonneg (y.edge_nonneg s t)
  omega

instance coarseFinite : Finite (CoarseData V n) := Finite.of_injective encode encode_injective
instance coarseFintype : Fintype (CoarseData V n) := Fintype.ofFinite _
instance coarseMeasurable : MeasurableSpace (CoarseData V n) := ⊤
instance coarseDiscrete : DiscreteMeasurableSpace (CoarseData V n) := ⟨fun _ => trivial⟩

def Regular (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) : Prop :=
  ∀ v t, |(d v t : ℝ) - p * (partSizes π t : ℝ)| ≤
    (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ)

def flag (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) : Bool := decide (Regular p π d)

@[simp] theorem flag_true (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) : flag p π d = true ↔ Regular p π d := by simp [flag]
@[simp] theorem flag_false (p : ℝ) (π : V → Universal.History (n+1))
    (d : V → Universal.History (n+1) → ℤ) : flag p π d = false ↔ ¬ Regular p π d := by simp [flag]

def rho (p : ℝ) (σ : State V n) : CoarseData V n where
  part := σ.part
  edge := edgeTotals σ.part σ.deg
  edge_symm := by obtain ⟨G,hG⟩ := σ.realizable; rw [← hG]; exact edgeTotals_symm σ.part G
  edge_even := by obtain ⟨G,hG⟩ := σ.realizable; rw [← hG]; exact edgeTotals_even σ.part G
  edge_nonneg := by obtain ⟨G,hG⟩ := σ.realizable; rw [← hG]; exact edgeTotals_nonneg σ.part G
  edge_upper := by
    obtain ⟨G,hG⟩ := σ.realizable
    rw [← hG]
    intro s t
    have h := edgeTotals_upper σ.part G s t
    simp only [block_card_partSizes] at h
    split_ifs at * <;> assumption
  reg := flag p σ.part σ.deg

@[simp] theorem rho_part (p : ℝ) (σ : State V n) : (rho p σ).part = σ.part := rfl
@[simp] theorem rho_edge (p : ℝ) (σ : State V n) : (rho p σ).edge = edgeTotals σ.part σ.deg := rfl
@[simp] theorem rho_reg (p : ℝ) (σ : State V n) : (rho p σ).reg = flag p σ.part σ.deg := rfl

def actualCoarse (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ) := rho p (actualState G c n)
def pAttainable (p : ℝ) (y : CoarseData V n) : Prop := ∃ σ, rho p σ = y

def initial (y : CoarseData V n) : V → Bool := fun v => Universal.bits (n+1) (y.part v) 0

def E (p : ℝ) (y : CoarseData V n) : Set (SimpleGraph V) :=
  {G | (∀ v, row (degreeArray y.part G) v ∈ Universal.historyEvent (y.part v)) ∧
    edgeTotals y.part (degreeArray y.part G) = y.edge ∧
    flag p y.part (degreeArray y.part G) = y.reg}

def rawState (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (hG : G ∈ E p y) : State V n where
  part := y.part
  deg := degreeArray y.part G
  realizable := ⟨G,rfl⟩
  history := hG.1

theorem rho_rawState (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (hG : G ∈ E p y) :
    rho p (rawState p y G hG) = y := coarse_ext rfl hG.2.1 hG.2.2

theorem actual_eq_raw (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (hG : G ∈ E p y)
    (c : V → Bool) (hc : CompatibleInitial y.part c) :
    actualState G c n = rawState p y G hG := reconstruction_state _ _ _ rfl hc

theorem actual_mem_E (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (c : V → Bool)
    (h : rho p (actualState G c n) = y) : G ∈ E p y := by
  have hpart := congrArg CoarseData.part h
  have hedge := congrArg CoarseData.edge h
  have hreg := congrArg CoarseData.reg h
  change (actualState G c n).part = y.part at hpart
  change edgeTotals (actualState G c n).part (actualState G c n).deg = y.edge at hedge
  change flag p (actualState G c n).part (actualState G c n).deg = y.reg at hreg
  have hd : (actualState G c n).deg = degreeArray y.part G := by rw [actualState_deg, ← hpart]; rfl
  rw [hd,hpart] at hedge hreg
  refine ⟨?_,hedge,hreg⟩
  intro v
  simpa only [hd,hpart] using (actualState G c n).history v

theorem E_iff_actual (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V)
    (c : V → Bool) (hc : CompatibleInitial y.part c) :
    G ∈ E p y ↔ rho p (actualState G c n) = y := by
  constructor
  · intro hG; rw [actual_eq_raw p y G hG c hc]; exact rho_rawState p y G hG
  · exact actual_mem_E p y G c

theorem E_nonempty_iff (p : ℝ) (y : CoarseData V n) : (E p y).Nonempty ↔ pAttainable p y := by
  constructor
  · rintro ⟨G,hG⟩; exact ⟨rawState p y G hG, rho_rawState p y G hG⟩
  · rintro ⟨σ,rfl⟩
    obtain ⟨G,c,h⟩ := attained σ
    exact ⟨G, actual_mem_E p _ G c (by rw [h])⟩

theorem rho_eq_graph (p : ℝ) (σ : State V n) (G : SimpleGraph V)
    (hG : degreeArray σ.part G = σ.deg) :
    rho p σ = toCoarseData σ.part G (flag p σ.part σ.deg) := by
  refine coarse_ext (x := rho p σ) (y := toCoarseData σ.part G (flag p σ.part σ.deg)) rfl ?_ rfl
  change edgeTotals σ.part σ.deg = edgeTotals σ.part (degreeArray σ.part G)
  rw [hG]

theorem actualCoarse_part (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    (actualCoarse p G c n).part = actualHistory G c (n+1) := rfl

theorem actualCoarse_edge (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    (actualCoarse p G c n).edge =
      edgeTotals (actualHistory G c (n+1)) (degreeArray (actualHistory G c (n+1)) G) := rfl

theorem actualCoarse_diagonal (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ)
    (s : Universal.History (n+1)) : (actualCoarse p G c n).edge s s =
      2 * (internalEdgeCount (actualHistory G c (n+1)) G s : ℤ) :=
  edgeTotals_diagonal _ _ _

theorem actualCoarse_reg (p : ℝ) (G : SimpleGraph V) (c : V → Bool) (n : ℕ) :
    (actualCoarse p G c n).reg =
      flag p (actualHistory G c (n+1)) (degreeArray (actualHistory G c (n+1)) G) := rfl

theorem raw_agreement (p : ℝ) (y : CoarseData V n) (G : SimpleGraph V) (hG : G ∈ E p y) :
    (actualState G (initial y) n).part = y.part ∧
    (actualState G (initial y) n).deg = degreeArray y.part G ∧
    rho p (actualState G (initial y) n) = y := by
  rw [actual_eq_raw p y G hG (initial y) (fun _ => rfl)]
  exact ⟨rfl,rfl,rho_rawState p y G hG⟩

end MajorityDynamics.GraphProcess.CoarseKernel
