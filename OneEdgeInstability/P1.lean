import Mathlib

set_option linter.style.header false

/-!
# P1: the filtered-graph counterexample family

This file formalizes the `H₀` counterexample family in the accompanying
preprint.  The proof uses only the finite filtered-graph construction described
there.

The public definitions below deliberately expose the two bridges on which the
terminology in the theorem rests:

* degree-zero homology of a finite graph is the free vector space on its
  connected components, so its dimension is the component count;
* the `KR₁` quantity is the infimum of the costs of genuine nonnegative
  couplings between the positive and negative unit atoms, with the `ℓ¹`
  ground metric.

Thus neither the Hilbert signed measure nor its transport norm is represented
by a finite computation trusted from outside Lean.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

namespace OneEdgeInstability.P1

/-! ## The finite graph and its integer grades -/

/-- Integer lattice grades.  All filtration grades in the construction have
this form, even though sublevel parameters are allowed to be real. -/
abbrev Grade (n : ℕ) := Fin n → ℤ

/-- Real parameters, used for sublevel sets and the ground metric. -/
abbrev RealGrade (n : ℕ) := Fin n → ℝ

/-- Coordinatewise comparison of an integer grade with a real parameter. -/
def Grade.leReal {n : ℕ} (a : Grade n) (x : RealGrade n) : Prop :=
  ∀ i, (a i : ℝ) ≤ x i

/-- The integer-lattice `ℓ¹` distance. -/
def l1Distance {n : ℕ} (x y : Grade n) : ℕ :=
  ∑ i, Int.natAbs (x i - y i)

/-- The real `ℓ¹` ground distance used by the Kantorovich problem. -/
def realL1Distance {n : ℕ} (x y : RealGrade n) : ℝ :=
  ∑ i, |x i - y i|

@[simp]
theorem l1Distance_self {n : ℕ} (x : Grade n) : l1Distance x x = 0 := by
  simp [l1Distance]

@[simp]
theorem realL1Distance_self {n : ℕ} (x : RealGrade n) : realL1Distance x x = 0 := by
  simp [realL1Distance]

/-- Vertices `s,t,u₁,…,uₘ` of the graph `Sₘ`.  A `Fin m` index `j`
represents the paper's index `j+1`. -/
inductive Vertex (m : ℕ)
  | s
  | t
  | u (j : Fin m)
  deriving DecidableEq, Fintype

/-- Edges `e,a₁,…,aₘ,b₁,…,bₘ` of `Sₘ`. -/
inductive Edge (m : ℕ)
  | e
  | a (j : Fin m)
  | b (j : Fin m)
  deriving DecidableEq, Fintype

/-- The zero- and one-simplices of `Sₘ`. -/
inductive Simplex (m : ℕ)
  | vertex (v : Vertex m)
  | edge (e : Edge m)
  deriving DecidableEq, Fintype

/-- The two endpoints of an edge. -/
def endpoints {m : ℕ} : Edge m → Finset (Vertex m)
  | .e => {.s, .t}
  | .a j => {.s, .u j}
  | .b j => {.u j, .t}

/-- The concrete finite graph, independent of the filtration. -/
def graph (m : ℕ) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun v w ↦ ∃ e : Edge m, v ∈ endpoints e ∧ w ∈ endpoints e

/-- Coordinatewise order on integer grades. -/
def Grade.LE {n : ℕ} (x y : Grade n) : Prop := ∀ i, x i ≤ y i

/-- Monotonicity for a filtration of the graph: every edge grade dominates
the grades of both endpoints. -/
def MonotoneFiltration {m n : ℕ} (F : Simplex m → Grade n) : Prop :=
  ∀ e v, v ∈ endpoints e → Grade.LE (F (.vertex v)) (F (.edge e))

/-- The filtration `fₘ` in three parameters. -/
def fGrade (m : ℕ) : Simplex m → Grade 3
  | .vertex _ => ![0, 0, 0]
  | .edge .e => ![2, 0, 0]
  | .edge (.a j) => ![0, (j.1 + 1 : ℕ), 0]
  | .edge (.b j) => ![0, 0, m - j.1]

/-- The filtration `gₘ` in three parameters.  It differs from `fₘ` only at
the central edge `e`. -/
def gGrade (m : ℕ) : Simplex m → Grade 3
  | .vertex _ => ![0, 0, 0]
  | .edge .e => ![1, 0, 0]
  | .edge (.a j) => ![0, (j.1 + 1 : ℕ), 0]
  | .edge (.b j) => ![0, 0, m - j.1]

theorem fGrade_monotone (m : ℕ) : MonotoneFiltration (fGrade m) := by
  intro e v hv i
  fin_cases i <;> cases e <;> simp_all [endpoints, fGrade] <;> positivity

theorem gGrade_monotone (m : ℕ) : MonotoneFiltration (gGrade m) := by
  intro e v hv i
  fin_cases i <;> cases e <;> simp_all [endpoints, gGrade] <;> positivity

/-- Sum, over every simplex, of the `ℓ¹` displacement of its grade.  This is
the finite-complex `ℓ¹` norm used in the source theorem. -/
def filtrationL1Distance {m n : ℕ} (F G : Simplex m → Grade n) : ℕ :=
  ∑ σ, l1Distance (F σ) (G σ)

theorem filtrationL1Distance_fGrade_gGrade (m : ℕ) :
    filtrationL1Distance (fGrade m) (gGrade m) = 1 := by
  classical
  rw [filtrationL1Distance, Finset.sum_eq_single (.edge .e)]
  · norm_num [l1Distance, fGrade, gGrade, Fin.sum_univ_succ]
  · intro σ _ hσ
    cases σ with
    | vertex v => simp [l1Distance, fGrade, gGrade]
    | edge e => cases e <;> simp_all [l1Distance, fGrade, gGrade]
  · simp

/-! ## Real sublevel graphs and ordinary degree-zero homology -/

/-- Whether an edge is present at a real parameter. -/
def edgeActive {m n : ℕ} (F : Simplex m → Grade n) (x : RealGrade n) (e : Edge m) : Prop :=
  Grade.leReal (F (.edge e)) x

/-- Whether the common vertex grade `(0,…,0)` is present. -/
def verticesActive {m n : ℕ} (F : Simplex m → Grade n) (x : RealGrade n) : Prop :=
  Grade.leReal (F (.vertex (.s : Vertex m))) x

/-- The graph carried by the sublevel complex.  Its vertex type is kept fixed;
`ordinaryH0Dim` below returns zero before the common vertex grade is active. -/
def sublevelGraph {m n : ℕ} (F : Simplex m → Grade n) (x : RealGrade n) :
    SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun v w ↦
    match v, w with
    | .s, .t => edgeActive F x .e
    | .s, .u j => edgeActive F x (.a j)
    | .u j, .t => edgeActive F x (.b j)
    | _, _ => False

/-- A transparent coordinate model for ordinary `H₀` of a finite graph over
the coefficient field `𝕜`: one coordinate for every connected component. -/
abbrev GraphH0 (𝕜 : Type*) {V : Type*} (G : SimpleGraph V) := G.ConnectedComponent → 𝕜

/-- The degree-zero Hilbert function of the filtered graph.  This is zero
before vertices enter and thereafter is the dimension of ordinary graph
`H₀`, equivalently the number of connected components. -/
noncomputable def ordinaryH0Dim {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) : ℕ := by
  classical
  exact if verticesActive F x then Nat.card (sublevelGraph F x).ConnectedComponent else 0

/-- The coordinate model of graph `H₀` has the expected component-count
dimension over every coefficient field. -/
theorem finrank_graphH0 (𝕜 : Type*) [Field 𝕜] {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    Module.finrank 𝕜 (GraphH0 𝕜 G) = Nat.card G.ConnectedComponent := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_pi 𝕜

/-! ### Component counts for the theta graph -/

/-- A theta graph in which the central edge and the two arms of every
two-edge path may be switched on independently. -/
def starGraph {m : ℕ} (left right : Fin m → Prop) (central : Prop) :
    SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun v w ↦
    match v, w with
    | .s, .t => central
    | .s, .u j => left j
    | .u j, .t => right j
    | _, _ => False

@[simp]
theorem starGraph_adj_s_t {m : ℕ} {left right : Fin m → Prop} {central : Prop} :
    (starGraph left right central).Adj .s .t ↔ central := by
  simp [starGraph]

@[simp]
theorem starGraph_adj_s_u {m : ℕ} {left right : Fin m → Prop} {central : Prop}
    (j : Fin m) :
    (starGraph left right central).Adj .s (.u j) ↔ left j := by
  simp [starGraph]

@[simp]
theorem starGraph_adj_u_t {m : ℕ} {left right : Fin m → Prop} {central : Prop}
    (j : Fin m) :
    (starGraph left right central).Adj (.u j) .t ↔ right j := by
  simp [starGraph]

/-- A quotient by graph reachability is equivalent to any surjective complete
set of component labels. -/
noncomputable def connectedComponentEquivOfLabel
    {V L : Type*} [Fintype V] [Fintype L]
    (G : SimpleGraph V) (label : V → L) (hsurj : Function.Surjective label)
    (hlabel : ∀ v w, G.Reachable v w ↔ label v = label w) :
    G.ConnectedComponent ≃ L where
  toFun := Quot.lift label fun v w h ↦ (hlabel v w).mp h
  invFun l := G.connectedComponentMk (Classical.choose (hsurj l))
  left_inv := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
        apply SimpleGraph.ConnectedComponent.eq.mpr
        apply (hlabel _ _).mpr
        exact Classical.choose_spec (hsurj (label v))
  right_inv := by
    intro l
    exact Classical.choose_spec (hsurj l)

/-- Indices of paths whose two arms are both absent.  Their middle vertices
are isolated components in either filtration. -/
def Detached {m : ℕ} (left right : Fin m → Prop) :=
  {j : Fin m // ¬ left j ∧ ¬ right j}

noncomputable instance instFintypeDetached {m : ℕ} (left right : Fin m → Prop) :
    Fintype (Detached left right) := by
  letI : Finite (Detached left right) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Component labels before the central edge appears, provided no complete
two-edge path joins `s` to `t`. -/
abbrev SplitLabel {m : ℕ} (left right : Fin m → Prop) :=
  Bool ⊕ Detached left right

/-- Component labels after `s` and `t` have become connected. -/
abbrev JoinedLabel {m : ℕ} (left right : Fin m → Prop) :=
  Unit ⊕ Detached left right

/-- The explicit split-component label of a vertex. -/
def splitLabel {m : ℕ} (left right : Fin m → Prop) [DecidablePred left]
    [DecidablePred right] : Vertex m → SplitLabel left right
  | .s => .inl false
  | .t => .inl true
  | .u j =>
      if hleft : left j then .inl false
      else if hright : right j then .inl true
      else .inr ⟨j, hleft, hright⟩

/-- The explicit joined-component label of a vertex. -/
def joinedLabel {m : ℕ} (left right : Fin m → Prop) [DecidablePred left]
    [DecidablePred right] : Vertex m → JoinedLabel left right
  | .s => .inl ()
  | .t => .inl ()
  | .u j =>
      if h : left j ∨ right j then .inl ()
      else .inr ⟨j, not_or.mp h⟩

theorem splitLabel_surjective {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] :
    Function.Surjective (splitLabel left right) := by
  rintro (b | j)
  · cases b
    · exact ⟨.s, rfl⟩
    · exact ⟨.t, rfl⟩
  · refine ⟨.u j.1, ?_⟩
    simp only [splitLabel, dif_neg j.2.1, dif_neg j.2.2]
    exact congrArg Sum.inr (Subtype.ext rfl)

theorem joinedLabel_surjective {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] :
    Function.Surjective (joinedLabel left right) := by
  rintro (u | j)
  · exact ⟨.s, rfl⟩
  · refine ⟨.u j.1, ?_⟩
    have hj : ¬ (left j.1 ∨ right j.1) := not_or.mpr j.2
    simp only [joinedLabel, dif_neg hj]
    exact congrArg Sum.inr (Subtype.ext rfl)

theorem splitLabel_eq_of_adj {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) {v w : Vertex m}
    (h : (starGraph left right False).Adj v w) :
    splitLabel left right v = splitLabel left right w := by
  have hright (j : Fin m) : right j → ¬ left j :=
    fun hr hl ↦ hdisjoint j ⟨hl, hr⟩
  rw [starGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h <;>
    cases v <;> cases w <;>
    simp_all [starGraph, splitLabel]

theorem splitLabel_eq_of_reachable {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) {v w : Vertex m}
    (h : (starGraph left right False).Reachable v w) :
    splitLabel left right v = splitLabel left right w := by
  rcases h with ⟨p⟩
  induction p with
  | nil => rfl
  | cons hAdj _ ih =>
      exact (splitLabel_eq_of_adj left right hdisjoint hAdj).trans ih

@[simp]
theorem splitLabel_u_eq_left {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (j : Fin m) :
    splitLabel left right (.u j) = .inl false ↔ left j := by
  by_cases hl : left j <;> by_cases hr : right j <;> simp [splitLabel, hl, hr]

@[simp]
theorem splitLabel_u_eq_right {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) (j : Fin m) :
    splitLabel left right (.u j) = .inl true ↔ right j := by
  by_cases hl : left j
  · have hr : ¬ right j := fun hj ↦ hdisjoint j ⟨hl, hj⟩
    simp [splitLabel, hl, hr]
  · simp [splitLabel, hl]

theorem splitLabel_reachable_of_eq {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) {v w : Vertex m}
    (h : splitLabel left right v = splitLabel left right w) :
    (starGraph left right False).Reachable v w := by
  let G := starGraph left right False
  have hsu (j : Fin m) (hj : left j) : G.Reachable .s (.u j) :=
    ((starGraph_adj_s_u j).mpr hj).reachable
  have hut (j : Fin m) (hj : right j) : G.Reachable (.u j) .t :=
    ((starGraph_adj_u_t j).mpr hj).reachable
  cases v with
  | s =>
      cases w with
      | s => exact .rfl
      | t => simp [splitLabel] at h
      | u j =>
          exact hsu j ((splitLabel_u_eq_left left right j).mp h.symm)
  | t =>
      cases w with
      | s => simp [splitLabel] at h
      | t => exact .rfl
      | u j =>
          exact (hut j ((splitLabel_u_eq_right left right hdisjoint j).mp h.symm)).symm
  | u j =>
      cases w with
      | s =>
          exact (hsu j ((splitLabel_u_eq_left left right j).mp h)).symm
      | t =>
          exact hut j ((splitLabel_u_eq_right left right hdisjoint j).mp h)
      | u k =>
          by_cases hjl : left j
          · have hkl : left k := by
              apply (splitLabel_u_eq_left left right k).mp
              rw [← h]
              exact (splitLabel_u_eq_left left right j).mpr hjl
            exact (hsu j hjl).symm.trans (hsu k hkl)
          · by_cases hjr : right j
            · have hkr : right k := by
                apply (splitLabel_u_eq_right left right hdisjoint k).mp
                rw [← h]
                exact (splitLabel_u_eq_right left right hdisjoint j).mpr hjr
              exact (hut j hjr).trans (hut k hkr).symm
            · have hjk : j = k := by
                by_cases hkl : left k
                · simp [splitLabel, hjl, hjr, hkl] at h
                · by_cases hkr : right k
                  · simp [splitLabel, hjl, hjr, hkl, hkr] at h
                  · rw [splitLabel, dif_neg hjl, dif_neg hjr, splitLabel,
                      dif_neg hkl, dif_neg hkr] at h
                    cases h
                    rfl
              subst k
              exact .rfl

theorem splitLabel_reachable_iff {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) (v w : Vertex m) :
    (starGraph left right False).Reachable v w ↔
      splitLabel left right v = splitLabel left right w :=
  ⟨splitLabel_eq_of_reachable left right hdisjoint,
    splitLabel_reachable_of_eq left right hdisjoint⟩

theorem joinedLabel_eq_of_adj {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (central : Prop)
    {v w : Vertex m} (h : (starGraph left right central).Adj v w) :
    joinedLabel left right v = joinedLabel left right w := by
  rw [starGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h <;>
    cases v <;> cases w <;>
    simp_all [starGraph, joinedLabel]

theorem joinedLabel_eq_of_reachable {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (central : Prop)
    {v w : Vertex m} (h : (starGraph left right central).Reachable v w) :
    joinedLabel left right v = joinedLabel left right w := by
  rcases h with ⟨p⟩
  induction p with
  | nil => rfl
  | cons hAdj _ ih =>
      exact (joinedLabel_eq_of_adj left right central hAdj).trans ih

@[simp]
theorem joinedLabel_u_eq_core {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (j : Fin m) :
    joinedLabel left right (.u j) = .inl () ↔ left j ∨ right j := by
  by_cases h : left j ∨ right j <;> simp [joinedLabel, h]

theorem joinedLabel_reachable_of_eq {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (central : Prop)
    (hjoined : central ∨ ∃ j, left j ∧ right j) {v w : Vertex m}
    (h : joinedLabel left right v = joinedLabel left right w) :
    (starGraph left right central).Reachable v w := by
  let G := starGraph left right central
  have hsu (j : Fin m) (hj : left j) : G.Reachable .s (.u j) :=
    ((starGraph_adj_s_u j).mpr hj).reachable
  have hut (j : Fin m) (hj : right j) : G.Reachable (.u j) .t :=
    ((starGraph_adj_u_t j).mpr hj).reachable
  have hst : G.Reachable .s .t := by
    rcases hjoined with hc | ⟨j, hjl, hjr⟩
    · exact ((starGraph_adj_s_t).mpr hc).reachable
    · exact (hsu j hjl).trans (hut j hjr)
  have hcore (j : Fin m) (hj : left j ∨ right j) : G.Reachable .s (.u j) := by
    rcases hj with hjl | hjr
    · exact hsu j hjl
    · exact hst.trans (hut j hjr).symm
  cases v with
  | s =>
      cases w with
      | s => exact .rfl
      | t => exact hst
      | u j =>
          exact hcore j ((joinedLabel_u_eq_core left right j).mp h.symm)
  | t =>
      cases w with
      | s => exact hst.symm
      | t => exact .rfl
      | u j =>
          exact hst.symm.trans (hcore j ((joinedLabel_u_eq_core left right j).mp h.symm))
  | u j =>
      cases w with
      | s =>
          exact (hcore j ((joinedLabel_u_eq_core left right j).mp h)).symm
      | t =>
          exact (hcore j ((joinedLabel_u_eq_core left right j).mp h)).symm.trans hst
      | u k =>
          by_cases hj : left j ∨ right j
          · have hk : left k ∨ right k := by
              apply (joinedLabel_u_eq_core left right k).mp
              rw [← h]
              exact (joinedLabel_u_eq_core left right j).mpr hj
            exact (hcore j hj).symm.trans (hcore k hk)
          · have hjk : j = k := by
              by_cases hk : left k ∨ right k
              · simp [joinedLabel, hj, hk] at h
              · have hs : (⟨j, not_or.mp hj⟩ : Detached left right) =
                    ⟨k, not_or.mp hk⟩ := by
                  rw [joinedLabel, dif_neg hj, joinedLabel, dif_neg hk] at h
                  cases h
                  rfl
                exact congrArg Subtype.val hs
            subst k
            exact .rfl

theorem joinedLabel_reachable_iff {m : ℕ} (left right : Fin m → Prop)
    [DecidablePred left] [DecidablePred right] (central : Prop)
    (hjoined : central ∨ ∃ j, left j ∧ right j) (v w : Vertex m) :
    (starGraph left right central).Reachable v w ↔
      joinedLabel left right v = joinedLabel left right w :=
  ⟨joinedLabel_eq_of_reachable left right central,
    joinedLabel_reachable_of_eq left right central hjoined⟩

noncomputable def splitComponentEquiv {m : ℕ} (left right : Fin m → Prop)
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) :
    (starGraph left right False).ConnectedComponent ≃ SplitLabel left right := by
  classical
  exact connectedComponentEquivOfLabel (starGraph left right False)
    (splitLabel left right) (splitLabel_surjective left right)
    (splitLabel_reachable_iff left right hdisjoint)

noncomputable def joinedComponentEquiv {m : ℕ} (left right : Fin m → Prop)
    (central : Prop) (hjoined : central ∨ ∃ j, left j ∧ right j) :
    (starGraph left right central).ConnectedComponent ≃ JoinedLabel left right := by
  classical
  exact connectedComponentEquivOfLabel (starGraph left right central)
    (joinedLabel left right) (joinedLabel_surjective left right)
    (joinedLabel_reachable_iff left right central hjoined)

theorem card_connectedComponent_split {m : ℕ} (left right : Fin m → Prop)
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) :
    Nat.card (starGraph left right False).ConnectedComponent =
      2 + Nat.card (Detached left right) := by
  classical
  calc
    Nat.card (starGraph left right False).ConnectedComponent =
        Nat.card (SplitLabel left right) :=
      Nat.card_congr (splitComponentEquiv left right hdisjoint)
    _ = 2 + Nat.card (Detached left right) := by simp [SplitLabel, Nat.card_sum]

theorem card_connectedComponent_joined {m : ℕ} (left right : Fin m → Prop)
    (central : Prop) (hjoined : central ∨ ∃ j, left j ∧ right j) :
    Nat.card (starGraph left right central).ConnectedComponent =
      1 + Nat.card (Detached left right) := by
  classical
  calc
    Nat.card (starGraph left right central).ConnectedComponent =
        Nat.card (JoinedLabel left right) :=
      Nat.card_congr (joinedComponentEquiv left right central hjoined)
    _ = 1 + Nat.card (Detached left right) := by simp [JoinedLabel, Nat.card_sum]

/-- Adding the central edge lowers the component count by exactly one when no
two-edge path was already complete. -/
theorem card_split_eq_card_joined_add_one {m : ℕ} (left right : Fin m → Prop)
    (hdisjoint : ∀ j, ¬ (left j ∧ right j)) :
    Nat.card (starGraph left right False).ConnectedComponent =
      Nat.card (starGraph left right True).ConnectedComponent + 1 := by
  rw [card_connectedComponent_split left right hdisjoint,
    card_connectedComponent_joined left right True (Or.inl trivial)]
  omega

/-- If a two-edge path is already complete, the central edge does not change
the component count. -/
theorem card_split_eq_card_joined_of_path {m : ℕ} (left right : Fin m → Prop)
    (hpath : ∃ j, left j ∧ right j) :
    Nat.card (starGraph left right False).ConnectedComponent =
      Nat.card (starGraph left right True).ConnectedComponent := by
  rw [card_connectedComponent_joined left right False (Or.inr hpath),
    card_connectedComponent_joined left right True (Or.inl trivial)]

/-- One extra component when the two core vertices are not joined. -/
noncomputable def splitComponentExtra (joined : Prop) : ℕ :=
  by
    classical
    exact if joined then 0 else 1

/-- Uniform component count for the theta graph: one core component, one for
each detached middle vertex, and one extra core component exactly when neither
the central edge nor a complete two-edge path joins `s` to `t`. -/
theorem card_connectedComponent_starGraph {m : ℕ}
    (left right : Fin m → Prop) (central : Prop) :
    Nat.card (starGraph left right central).ConnectedComponent =
      1 + Nat.card (Detached left right) +
        splitComponentExtra (central ∨ ∃ j, left j ∧ right j) := by
  classical
  by_cases hjoined : central ∨ ∃ j, left j ∧ right j
  · rw [card_connectedComponent_joined left right central hjoined,
      splitComponentExtra, if_pos hjoined]
    omega
  · have hcentral : ¬ central := fun hc ↦ hjoined (Or.inl hc)
    have hdisjoint : ∀ j, ¬ (left j ∧ right j) := by
      intro j hj
      exact hjoined (Or.inr ⟨j, hj⟩)
    have hgraph : starGraph left right central =
        starGraph left right False := by simp [hcentral]
    rw [hgraph, card_connectedComponent_split left right hdisjoint,
      splitComponentExtra, if_neg hjoined]
    omega

@[simp]
theorem sublevelGraph_eq_starGraph {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) :
    sublevelGraph F x = starGraph (fun j ↦ edgeActive F x (.a j))
      (fun j ↦ edgeActive F x (.b j)) (edgeActive F x .e) := rfl

theorem verticesActive_fGrade_iff (m : ℕ) (x : RealGrade 3) :
    verticesActive (fGrade m) x ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [verticesActive, Grade.leReal, fGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem verticesActive_gGrade_iff (m : ℕ) (x : RealGrade 3) :
    verticesActive (gGrade m) x ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [verticesActive, Grade.leReal, gGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_fGrade_e_iff (m : ℕ) (x : RealGrade 3) :
    edgeActive (fGrade m) x .e ↔ 2 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, fGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_gGrade_e_iff (m : ℕ) (x : RealGrade 3) :
    edgeActive (gGrade m) x .e ↔ 1 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, gGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_fGrade_a_iff (m : ℕ) (x : RealGrade 3) (j : Fin m) :
    edgeActive (fGrade m) x (.a j) ↔
      0 ≤ x 0 ∧ (j.1 + 1 : ℕ) ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, fGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_gGrade_a_iff (m : ℕ) (x : RealGrade 3) (j : Fin m) :
    edgeActive (gGrade m) x (.a j) ↔
      0 ≤ x 0 ∧ (j.1 + 1 : ℕ) ≤ x 1 ∧ 0 ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, gGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_fGrade_b_iff (m : ℕ) (x : RealGrade 3) (j : Fin m) :
    edgeActive (fGrade m) x (.b j) ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (m - j.1 : ℕ) ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, fGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

theorem edgeActive_gGrade_b_iff (m : ℕ) (x : RealGrade 3) (j : Fin m) :
    edgeActive (gGrade m) x (.b j) ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (m - j.1 : ℕ) ≤ x 2 := by
  simp only [edgeActive, Grade.leReal, gGrade]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> norm_num at * <;> assumption

/-- Activation of the `aⱼ` arm after the common vertex grade is present. -/
def leftAt (m : ℕ) (x : RealGrade 3) (j : Fin m) : Prop :=
  ((j.1 + 1 : ℕ) : ℝ) ≤ x 1

/-- Activation of the `bⱼ` arm after the common vertex grade is present. -/
def rightAt (m : ℕ) (x : RealGrade 3) (j : Fin m) : Prop :=
  ((m - j.1 : ℕ) : ℝ) ≤ x 2

theorem sublevelGraph_fGrade_eq (m : ℕ) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    sublevelGraph (fGrade m) x =
      starGraph (leftAt m x) (rightAt m x) (2 ≤ x 0) := by
  rw [sublevelGraph_eq_starGraph]
  congr 1
  · funext j
    exact propext <| (edgeActive_fGrade_a_iff m x j).trans <| by
      simp [leftAt, h0, h2]
  · funext j
    exact propext <| (edgeActive_fGrade_b_iff m x j).trans <| by
      simp [rightAt, h0, h1]
  · exact propext <| (edgeActive_fGrade_e_iff m x).trans <| by simp [h1, h2]

theorem sublevelGraph_gGrade_eq (m : ℕ) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    sublevelGraph (gGrade m) x =
      starGraph (leftAt m x) (rightAt m x) (1 ≤ x 0) := by
  rw [sublevelGraph_eq_starGraph]
  congr 1
  · funext j
    exact propext <| (edgeActive_gGrade_a_iff m x j).trans <| by
      simp [leftAt, h0, h2]
  · funext j
    exact propext <| (edgeActive_gGrade_b_iff m x j).trans <| by
      simp [rightAt, h0, h1]
  · exact propext <| (edgeActive_gGrade_e_iff m x).trans <| by simp [h1, h2]

theorem ordinaryH0Dim_fGrade_of_active (m : ℕ) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    ordinaryH0Dim (fGrade m) x =
      1 + Nat.card (Detached (leftAt m x) (rightAt m x)) +
        splitComponentExtra
          (2 ≤ x 0 ∨ ∃ j, leftAt m x j ∧ rightAt m x j) := by
  have hv : verticesActive (fGrade m) x :=
    (verticesActive_fGrade_iff m x).2 ⟨h0, h1, h2⟩
  rw [ordinaryH0Dim, if_pos hv, sublevelGraph_fGrade_eq m x h0 h1 h2,
    card_connectedComponent_starGraph]

theorem ordinaryH0Dim_gGrade_of_active (m : ℕ) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    ordinaryH0Dim (gGrade m) x =
      1 + Nat.card (Detached (leftAt m x) (rightAt m x)) +
        splitComponentExtra
          (1 ≤ x 0 ∨ ∃ j, leftAt m x j ∧ rightAt m x j) := by
  have hv : verticesActive (gGrade m) x :=
    (verticesActive_gGrade_iff m x).2 ⟨h0, h1, h2⟩
  rw [ordinaryH0Dim, if_pos hv, sublevelGraph_gGrade_eq m x h0 h1 h2,
    card_connectedComponent_starGraph]

/-- The staircase complement `qₘ(y,z)` used in the construction. -/
noncomputable def staircase (m : ℕ) (y z : ℝ) : ℤ :=
  if 0 ≤ y ∧ 0 ≤ z ∧
      ∀ j : Fin m, ¬ ((((j.1 + 1 : ℕ) : ℝ) ≤ y) ∧ (((m - j.1 : ℕ) : ℝ) ≤ z))
    then 1 else 0

/-- The half-open slab indicator `1_[1,2)(r)`. -/
noncomputable def slabIndicator (r : ℝ) : ℤ := if 1 ≤ r ∧ r < 2 then 1 else 0

/-- The integer-valued difference of the two ordinary `H₀` Hilbert functions. -/
noncomputable def h0HilbertDifference (m : ℕ) (x : RealGrade 3) : ℤ :=
  (ordinaryH0Dim (fGrade m) x : ℤ) - (ordinaryH0Dim (gGrade m) x : ℤ)

/-- The difference of the ordinary `H₀` Hilbert functions is a slab indicator
times the staircase complement. -/
theorem h0HilbertDifference_eq_slab_staircase (m : ℕ) (x : RealGrade 3) :
    h0HilbertDifference m x = slabIndicator (x 0) * staircase m (x 1) (x 2) := by
  classical
  by_cases h0 : 0 ≤ x 0
  · by_cases h1 : 0 ≤ x 1
    · by_cases h2 : 0 ≤ x 2
      · have hvf : verticesActive (fGrade m) x :=
          (verticesActive_fGrade_iff m x).mpr ⟨h0, h1, h2⟩
        have hvg : verticesActive (gGrade m) x :=
          (verticesActive_gGrade_iff m x).mpr ⟨h0, h1, h2⟩
        simp only [h0HilbertDifference, ordinaryH0Dim, if_pos hvf, if_pos hvg]
        rw [sublevelGraph_fGrade_eq m x h0 h1 h2,
          sublevelGraph_gGrade_eq m x h0 h1 h2]
        by_cases hr1 : 1 ≤ x 0
        · by_cases hr2 : 2 ≤ x 0
          · have hnlt2 : ¬ x 0 < 2 := not_lt.mpr hr2
            simp [hr1, hr2, slabIndicator, hnlt2]
          · have hlt2 : x 0 < 2 := lt_of_not_ge hr2
            by_cases hpath : ∃ j, leftAt m x j ∧ rightAt m x j
            · have hcard := card_split_eq_card_joined_of_path
                (leftAt m x) (rightAt m x) hpath
              have hstair : staircase m (x 1) (x 2) = 0 := by
                rw [staircase, if_neg]
                rintro ⟨_, _, hall⟩
                exact hpath.elim fun j hj ↦ hall j hj
              simp [hr1, hr2, hlt2, slabIndicator, hstair]
              have hcardF :
                  Fintype.card (starGraph (leftAt m x) (rightAt m x) False).ConnectedComponent =
                    Fintype.card (starGraph (leftAt m x) (rightAt m x) True).ConnectedComponent := by
                simpa only [Nat.card_eq_fintype_card] using hcard
              exact sub_eq_zero.mpr (congrArg (fun q : ℕ ↦ (q : ℤ)) hcardF)
            · have hdisjoint : ∀ j, ¬ (leftAt m x j ∧ rightAt m x j) :=
                not_exists.mp hpath
              have hcard := card_split_eq_card_joined_add_one
                (leftAt m x) (rightAt m x) hdisjoint
              have hstair : staircase m (x 1) (x 2) = 1 := by
                rw [staircase, if_pos]
                exact ⟨h1, h2, hdisjoint⟩
              simp [hr1, hr2, hlt2, slabIndicator, hstair]
              have hcardF :
                  Fintype.card (starGraph (leftAt m x) (rightAt m x) False).ConnectedComponent =
                    Fintype.card (starGraph (leftAt m x) (rightAt m x) True).ConnectedComponent + 1 := by
                simpa only [Nat.card_eq_fintype_card] using hcard
              rw [hcardF]
              push_cast
              ring
        · have hr2 : ¬ 2 ≤ x 0 := by linarith
          simp [hr1, hr2, slabIndicator]
      · have hvf : ¬ verticesActive (fGrade m) x := by
          rw [verticesActive_fGrade_iff]
          tauto
        have hvg : ¬ verticesActive (gGrade m) x := by
          rw [verticesActive_gGrade_iff]
          tauto
        simp [h0HilbertDifference, ordinaryH0Dim, hvf, hvg, staircase, h2]
    · have hvf : ¬ verticesActive (fGrade m) x := by
        rw [verticesActive_fGrade_iff]
        tauto
      have hvg : ¬ verticesActive (gGrade m) x := by
        rw [verticesActive_gGrade_iff]
        tauto
      simp [h0HilbertDifference, ordinaryH0Dim, hvf, hvg, staircase, h1]
  · have hvf : ¬ verticesActive (fGrade m) x := by
      rw [verticesActive_fGrade_iff]
      tauto
    have hvg : ¬ verticesActive (gGrade m) x := by
      rw [verticesActive_gGrade_iff]
      tauto
    have hr1 : ¬ 1 ≤ x 0 := by linarith
    simp [h0HilbertDifference, ordinaryH0Dim, hvf, hvg, slabIndicator, hr1]

/-! ## Finite Hilbert decomposition signed measures -/

/-- Coordinatewise order on real grades. -/
def RealGrade.LE {n : ℕ} (a x : RealGrade n) : Prop := ∀ i, a i ≤ x i

/-- A finite signed point measure, represented by its integer atom
multiplicities.  `toSignedMeasure` below realizes it as an actual mathlib
signed measure made from Dirac masses. -/
abbrev AtomicSignedMeasure (n : ℕ) := RealGrade n →₀ ℤ

/-- A unit Dirac atom in the finite representation. -/
noncomputable def atom {n : ℕ} (a : RealGrade n) : AtomicSignedMeasure n :=
  Finsupp.single a 1

/-- The coefficient map used for one lower-orthant query. -/
noncomputable def lowerCoefficientHom {n : ℕ} (a x : RealGrade n) : ℤ →+ ℤ := by
  classical
  exact if RealGrade.LE a x then AddMonoidHom.id ℤ else 0

@[simp]
theorem lowerCoefficientHom_apply_of_le {n : ℕ} (a x : RealGrade n) (c : ℤ)
    (h : RealGrade.LE a x) : lowerCoefficientHom a x c = c := by
  classical
  simp [lowerCoefficientHom, h]

@[simp]
theorem lowerCoefficientHom_apply_of_not_le {n : ℕ} (a x : RealGrade n) (c : ℤ)
    (h : ¬ RealGrade.LE a x) : lowerCoefficientHom a x c = 0 := by
  classical
  simp [lowerCoefficientHom, h]

/-- Lower-orthant indicator of a single atom. -/
noncomputable def lowerIndicator {n : ℕ} (a x : RealGrade n) : ℤ :=
  lowerCoefficientHom a x 1

/-- Value of a finite signed point measure on the lower orthant `(-∞,x]`. -/
noncomputable def cumulative {n : ℕ} (μ : AtomicSignedMeasure n) (x : RealGrade n) : ℤ := by
  classical
  exact μ.sum fun a ↦ lowerCoefficientHom a x

@[simp]
theorem cumulative_atom {n : ℕ} (a x : RealGrade n) :
    cumulative (atom a) x = lowerIndicator a x := by
  classical
  simp [cumulative, atom, lowerIndicator]

theorem cumulative_single {n : ℕ} (a : RealGrade n) (c : ℤ) (x : RealGrade n) :
    cumulative (Finsupp.single a c) x = lowerCoefficientHom a x c := by
  classical
  simp [cumulative]

theorem cumulative_add {n : ℕ} (μ ν : AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (μ + ν) x = cumulative μ x + cumulative ν x := by
  classical
  simp [cumulative]

theorem cumulative_neg {n : ℕ} (μ : AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (-μ) x = -cumulative μ x := by
  classical
  have h : cumulative μ x + cumulative (-μ) x = 0 := by
    rw [← cumulative_add]
    simp [cumulative]
  omega

theorem cumulative_sub {n : ℕ} (μ ν : AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (μ - ν) x = cumulative μ x - cumulative ν x := by
  rw [sub_eq_add_neg, cumulative_add, cumulative_neg, sub_eq_add_neg]

/-- Cumulative evaluation as an additive homomorphism in the measure. -/
noncomputable def cumulativeAddHom {n : ℕ} (x : RealGrade n) :
    AtomicSignedMeasure n →+ ℤ where
  toFun μ := cumulative μ x
  map_zero' := by classical simp [cumulative]
  map_add' μ ν := cumulative_add μ ν x

@[simp]
theorem cumulativeAddHom_apply {n : ℕ} (x : RealGrade n) (μ : AtomicSignedMeasure n) :
    cumulativeAddHom x μ = cumulative μ x := rfl

/-- A finite signed point measure is a Hilbert decomposition of `h` exactly
when all of its lower-orthant cumulative values equal `h`. -/
def IsHilbertDecomposition {n : ℕ} (h : RealGrade n → ℤ)
    (μ : AtomicSignedMeasure n) : Prop :=
  ∀ x, cumulative μ x = h x

/-- Sum of coordinates, used only to select a minimal atom in the uniqueness
proof. -/
def coordinateWeight {n : ℕ} (a : RealGrade n) : ℝ := ∑ i, a i

theorem coordinateWeight_lt_of_le_of_ne {n : ℕ} {a b : RealGrade n}
    (hle : RealGrade.LE a b) (hne : a ≠ b) : coordinateWeight a < coordinateWeight b := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  apply Finset.sum_lt_sum (fun j _ ↦ hle j)
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hle i) hi⟩

theorem exists_coordinatewise_minimal_atom {n : ℕ} {μ : AtomicSignedMeasure n}
    (hμ : μ ≠ 0) :
    ∃ a ∈ μ.support, ∀ b ∈ μ.support, RealGrade.LE b a → b = a := by
  classical
  obtain ⟨a, ha, hmin⟩ :=
    Finset.exists_min_image μ.support coordinateWeight (Finsupp.support_nonempty_iff.mpr hμ)
  refine ⟨a, ha, ?_⟩
  intro b hb hle
  by_contra hne
  exact (not_lt_of_ge (hmin b hb)) (coordinateWeight_lt_of_le_of_ne hle hne)

theorem cumulative_eq_coefficient_of_minimal {n : ℕ} {μ : AtomicSignedMeasure n}
    {a : RealGrade n} (ha : a ∈ μ.support)
    (hmin : ∀ b ∈ μ.support, RealGrade.LE b a → b = a) :
    cumulative μ a = μ a := by
  classical
  change μ.support.sum (fun b ↦ lowerCoefficientHom b a (μ b)) = μ a
  have haa : lowerCoefficientHom a a (μ a) = μ a := by
    apply lowerCoefficientHom_apply_of_le
    intro i
    rfl
  rw [← haa]
  apply Finset.sum_eq_single a
  · intro b hb hba
    have hnle : ¬ RealGrade.LE b a := fun hle ↦ hba (hmin b hb hle)
    simp [hnle]
  · exact fun h ↦ (h ha).elim

/-- Finite signed point measures are uniquely determined by all lower-orthant
cumulative values.  This is the finite uniqueness bridge used to identify the
Hilbert decomposition measure, rather than merely an analogous atom formula. -/
theorem atomicSignedMeasure_ext {n : ℕ} {μ ν : AtomicSignedMeasure n}
    (h : ∀ x, cumulative μ x = cumulative ν x) : μ = ν := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨a, ha, hmin⟩ := exists_coordinatewise_minimal_atom hne
  have hzero : cumulative (μ - ν) a = 0 := by
    rw [cumulative_sub, h a, sub_self]
  have hcoeff := cumulative_eq_coefficient_of_minimal ha hmin
  exact (Finsupp.mem_support_iff.mp ha) (hcoeff ▸ hzero)

theorem IsHilbertDecomposition.unique {n : ℕ} {h : RealGrade n → ℤ}
    {μ ν : AtomicSignedMeasure n} (hμ : IsHilbertDecomposition h μ)
    (hν : IsHilbertDecomposition h ν) : μ = ν :=
  atomicSignedMeasure_ext fun x ↦ (hμ x).trans (hν x).symm

/-- The lower orthant represented by a cumulative query. -/
def lowerOrthant {n : ℕ} (x : RealGrade n) : Set (RealGrade n) :=
  {a | RealGrade.LE a x}

theorem measurableSet_lowerOrthant {n : ℕ} (x : RealGrade n) :
    MeasurableSet (lowerOrthant x) := by
  change MeasurableSet {a : Fin n → ℝ | ∀ i, a i ≤ x i}
  rw [show {a : Fin n → ℝ | ∀ i, a i ≤ x i} =
      ⋂ i, {a : Fin n → ℝ | a i ≤ x i} by ext a; simp]
  exact MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (measurable_pi_apply i)

/-- Realization of the finite coefficient representation as an actual signed
measure in mathlib: a finite real linear combination of Dirac measures. -/
noncomputable def AtomicSignedMeasure.toSignedMeasure {n : ℕ}
    (μ : AtomicSignedMeasure n) : MeasureTheory.SignedMeasure (RealGrade n) :=
  μ.sum fun a c ↦ (c : ℝ) • (Measure.dirac a).toSignedMeasure

theorem AtomicSignedMeasure.toSignedMeasure_add {n : ℕ}
    (μ ν : AtomicSignedMeasure n) :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  classical
  simp [AtomicSignedMeasure.toSignedMeasure, Finsupp.sum_add_index', add_smul]

theorem AtomicSignedMeasure.toSignedMeasure_neg {n : ℕ}
    (mu : AtomicSignedMeasure n) :
    (-mu).toSignedMeasure = -mu.toSignedMeasure := by
  have h : mu.toSignedMeasure + (-mu).toSignedMeasure = 0 := by
    rw [← AtomicSignedMeasure.toSignedMeasure_add]
    simp [AtomicSignedMeasure.toSignedMeasure]
  exact eq_neg_of_add_eq_zero_right h

theorem AtomicSignedMeasure.toSignedMeasure_sub {n : ℕ}
    (mu nu : AtomicSignedMeasure n) :
    (mu - nu).toSignedMeasure = mu.toSignedMeasure - nu.toSignedMeasure := by
  simp [sub_eq_add_neg, AtomicSignedMeasure.toSignedMeasure_add,
    AtomicSignedMeasure.toSignedMeasure_neg]

theorem AtomicSignedMeasure.toSignedMeasure_single_apply_lowerOrthant {n : ℕ}
    (a : RealGrade n) (c : ℤ) (x : RealGrade n) :
    AtomicSignedMeasure.toSignedMeasure (Finsupp.single a c : AtomicSignedMeasure n)
        (lowerOrthant x) =
      (lowerCoefficientHom a x c : ℝ) := by
  classical
  have hs : MeasurableSet (lowerOrthant x) := measurableSet_lowerOrthant x
  rw [AtomicSignedMeasure.toSignedMeasure, Finsupp.sum_single_index]
  · rw [_root_.smul_apply, Measure.toSignedMeasure_apply_measurable hs,
      Measure.real_def, Measure.dirac_apply' a hs]
    by_cases h : RealGrade.LE a x
    · simp [lowerOrthant, h, lowerCoefficientHom]
    · simp [lowerOrthant, h, lowerCoefficientHom]
  · simp

/-- The finite cumulative definition is exactly evaluation of the genuine
signed Dirac measure on a lower orthant. -/
theorem AtomicSignedMeasure.toSignedMeasure_apply_lowerOrthant {n : ℕ}
    (μ : AtomicSignedMeasure n) (x : RealGrade n) :
    μ.toSignedMeasure (lowerOrthant x) = (cumulative μ x : ℝ) := by
  classical
  induction μ using Finsupp.induction with
  | zero => simp [AtomicSignedMeasure.toSignedMeasure, cumulative]
  | single_add a c μ ha hc ih =>
      rw [AtomicSignedMeasure.toSignedMeasure_add, cumulative_add]
      change
        AtomicSignedMeasure.toSignedMeasure (Finsupp.single a c) (lowerOrthant x) +
            AtomicSignedMeasure.toSignedMeasure μ (lowerOrthant x) =
          ((cumulative (Finsupp.single a c) x + cumulative μ x : ℤ) : ℝ)
      rw [ih, AtomicSignedMeasure.toSignedMeasure_single_apply_lowerOrthant,
        cumulative_single]
      norm_num

/-! ### The staircase Möbius measure -/

/-- The paper's point `pⱼ=(j+1,m-j)` with a natural-number index.  The
range-based version makes prefix induction transparent. -/
def pathPointNat (m j : ℕ) : RealGrade 2 :=
  ![((j + 1 : ℕ) : ℝ), ((m - j : ℕ) : ℝ)]

/-- The adjacent join following `pⱼ`, with a natural-number index. -/
def cornerPointNat (m j : ℕ) : RealGrade 2 :=
  ![((j + 2 : ℕ) : ℝ), ((m - j : ℕ) : ℝ)]

/-- The paper's point `pⱼ=(j,m+1-j)`, with a zero-based `Fin m` index. -/
def pathPoint (m : ℕ) (j : Fin m) : RealGrade 2 :=
  pathPointNat m j.1

/-- The adjacent join `cⱼ=(j+1,m+1-j)`, again with zero-based indexing. -/
def cornerPoint (m : ℕ) (j : Fin (m - 1)) : RealGrade 2 :=
  cornerPointNat m j.1

/-- The signed atomic measure
`νₘ=δ_(0,0)-∑δ_pⱼ+∑δ_cⱼ`. -/
noncomputable def staircaseMeasure (m : ℕ) : AtomicSignedMeasure 2 :=
  atom ![0, 0] - (∑ j ∈ Finset.range m, atom (pathPointNat m j)) +
    ∑ j ∈ Finset.range (m - 1), atom (cornerPointNat m j)

/-- The range-indexed definition is the Möbius atom formula for the
staircase. -/
theorem staircaseMeasure_eq_pdf_formula (m : ℕ) :
    staircaseMeasure m =
      atom ![0, 0] - (∑ j : Fin m, atom (pathPoint m j)) +
        ∑ j : Fin (m - 1), atom (cornerPoint m j) := by
  have hp : (∑ j : Fin m, atom (pathPoint m j)) =
      ∑ j ∈ Finset.range m, atom (pathPointNat m j) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, pathPoint]
  have hc : (∑ j : Fin (m - 1), atom (cornerPoint m j)) =
      ∑ j ∈ Finset.range (m - 1), atom (cornerPointNat m j) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, cornerPoint]
  rw [staircaseMeasure, hp, hc]

/-- Concatenation of parameter vectors. -/
def concatGrade {n k : ℕ} (x : RealGrade n) (y : RealGrade k) : RealGrade (n + k) :=
  Fin.addCases x y

theorem concatGrade_le_iff {n k : ℕ} (a x : RealGrade n) (b y : RealGrade k) :
    RealGrade.LE (concatGrade a b) (concatGrade x y) ↔
      RealGrade.LE a x ∧ RealGrade.LE b y := by
  constructor
  · intro h
    exact ⟨fun i ↦ by simpa [concatGrade] using h (Fin.castAdd k i),
      fun j ↦ by simpa [concatGrade] using h (Fin.natAdd n j)⟩
  · rintro ⟨ha, hb⟩ i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [concatGrade] using ha j
    · simpa [concatGrade] using hb j

/-- Tensor product of two finite signed atomic measures. -/
noncomputable def AtomicSignedMeasure.tensor {n k : ℕ}
    (μ : AtomicSignedMeasure n) (ν : AtomicSignedMeasure k) :
    AtomicSignedMeasure (n + k) :=
  μ.sum fun a ca ↦ ν.sum fun b cb ↦ (ca * cb) • atom (concatGrade a b)

theorem AtomicSignedMeasure.tensor_add_left {n k : ℕ}
    (μ₁ μ₂ : AtomicSignedMeasure n) (ν : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor (μ₁ + μ₂) ν =
      AtomicSignedMeasure.tensor μ₁ ν + AtomicSignedMeasure.tensor μ₂ ν := by
  classical
  simp [AtomicSignedMeasure.tensor, Finsupp.sum_add_index', add_mul, add_smul]

theorem AtomicSignedMeasure.tensor_add_right {n k : ℕ}
    (μ : AtomicSignedMeasure n) (ν₁ ν₂ : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor μ (ν₁ + ν₂) =
      AtomicSignedMeasure.tensor μ ν₁ + AtomicSignedMeasure.tensor μ ν₂ := by
  classical
  simp [AtomicSignedMeasure.tensor, Finsupp.sum_add_index', mul_add, add_smul,
    Finsupp.sum_add]

theorem AtomicSignedMeasure.tensor_single_single {n k : ℕ}
    (a : RealGrade n) (ca : ℤ) (b : RealGrade k) (cb : ℤ) :
    AtomicSignedMeasure.tensor (Finsupp.single a ca) (Finsupp.single b cb) =
      (ca * cb) • atom (concatGrade a b) := by
  classical
  simp [AtomicSignedMeasure.tensor]

/-- The one-dimensional signed measure `η=δ₁-δ₂`. -/
noncomputable def slabMeasure : AtomicSignedMeasure 1 := atom ![1] - atom ![2]

/-- The candidate Hilbert-decomposition difference `Δₘ=η⊗νₘ`. -/
noncomputable def hilbertDifferenceMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor slabMeasure (staircaseMeasure m)

theorem cumulative_smul {n : ℕ} (c : ℤ) (μ : AtomicSignedMeasure n)
    (x : RealGrade n) : cumulative (c • μ) x = c * cumulative μ x := by
  classical
  simpa [smul_eq_mul] using (cumulativeAddHom x).map_zsmul c μ

theorem cumulative_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (μ : ι → AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (∑ i ∈ s, μ i) x = ∑ i ∈ s, cumulative (μ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cumulative]
  | @insert a s ha ih => simp [ha, cumulative_add, ih]

theorem cumulative_fintype_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (∑ i, μ i) x = ∑ i, cumulative (μ i) x := by
  classical
  simpa using cumulative_finset_sum (Finset.univ : Finset ι) μ x

theorem cumulative_tensor_single_left {n k : ℕ} (a : RealGrade n) (ca : ℤ)
    (ν : AtomicSignedMeasure k) (x : RealGrade n) (y : RealGrade k) :
    cumulative (AtomicSignedMeasure.tensor (Finsupp.single a ca) ν) (concatGrade x y) =
      cumulative (Finsupp.single a ca) x * cumulative ν y := by
  classical
  induction ν using Finsupp.induction with
  | zero => simp [AtomicSignedMeasure.tensor, cumulative]
  | single_add b cb ν hb hcb ih =>
      rw [AtomicSignedMeasure.tensor_add_right, cumulative_add, cumulative_add, ih]
      rw [AtomicSignedMeasure.tensor_single_single, cumulative_smul,
        cumulative_single, cumulative_single]
      by_cases hax : RealGrade.LE a x <;>
        by_cases hby : RealGrade.LE b y <;>
        simp [lowerIndicator, concatGrade_le_iff, hax, hby]
      ring

theorem cumulative_tensor {n k : ℕ} (μ : AtomicSignedMeasure n)
    (ν : AtomicSignedMeasure k) (x : RealGrade n) (y : RealGrade k) :
    cumulative (AtomicSignedMeasure.tensor μ ν) (concatGrade x y) =
      cumulative μ x * cumulative ν y := by
  classical
  induction μ using Finsupp.induction with
  | zero => simp [AtomicSignedMeasure.tensor, cumulative]
  | single_add a ca μ ha hca ih =>
      rw [AtomicSignedMeasure.tensor_add_left, cumulative_add, cumulative_add, ih,
        cumulative_tensor_single_left]
      ring

/-- Möbius measure of a one-dimensional half-open interval `[a,b)`. -/
noncomputable def halfOpenIntervalMeasure (a b : ℝ) : AtomicSignedMeasure 1 :=
  atom ![a] - atom ![b]

theorem cumulative_halfOpenIntervalMeasure (a b : ℝ) (hab : a ≤ b)
    (x : RealGrade 1) :
    cumulative (halfOpenIntervalMeasure a b) x =
      if a ≤ x 0 ∧ x 0 < b then 1 else 0 := by
  classical
  by_cases ha : a ≤ x 0
  · by_cases hb : b ≤ x 0
    · have hnb : ¬ x 0 < b := not_lt.mpr hb
      simp [halfOpenIntervalMeasure, cumulative_sub, cumulative_atom,
        lowerIndicator, lowerCoefficientHom, RealGrade.LE, ha, hb, hnb]
    · have hxb : x 0 < b := lt_of_not_ge hb
      simp [halfOpenIntervalMeasure, cumulative_sub, cumulative_atom,
        lowerIndicator, lowerCoefficientHom, RealGrade.LE, ha, hb, hxb]
  · have hb : ¬ b ≤ x 0 := fun hbx ↦ ha (hab.trans hbx)
    simp [halfOpenIntervalMeasure, cumulative_sub, cumulative_atom,
      lowerIndicator, lowerCoefficientHom, RealGrade.LE, ha, hb]

/-- One summand for a detached middle vertex: the box
`[0,∞) × [0,j+1) × [0,m-j)`. -/
noncomputable def detachedBoxMeasure (m : ℕ) (j : Fin m) :
    AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (atom ![0])
    (AtomicSignedMeasure.tensor
      (halfOpenIntervalMeasure 0 (j.1 + 1 : ℕ))
      (halfOpenIntervalMeasure 0 (m - j.1 : ℕ)))

theorem cumulative_detachedBoxMeasure (m : ℕ) (j : Fin m)
    (x : RealGrade 3) :
    cumulative (detachedBoxMeasure m j) x =
      if 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 < (j.1 + 1 : ℕ) ∧
          0 ≤ x 2 ∧ x 2 < (m - j.1 : ℕ) then 1 else 0 := by
  classical
  let xr : RealGrade 1 := ![x 0]
  let xy : RealGrade 1 := ![x 1]
  let xz : RealGrade 1 := ![x 2]
  have hx : concatGrade xr (concatGrade xy xz) = x := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [← hx]
  rw [detachedBoxMeasure, cumulative_tensor, cumulative_tensor,
    cumulative_halfOpenIntervalMeasure 0 (j.1 + 1 : ℕ) (by positivity),
    cumulative_halfOpenIntervalMeasure 0 (m - j.1 : ℕ) (by positivity)]
  simp only [cumulative_atom, lowerIndicator, lowerCoefficientHom,
    RealGrade.LE, Fin.isValue, Matrix.cons_val_zero, ite_mul, mul_ite,
    one_mul, zero_mul]
  by_cases h0 : 0 ≤ x 0 <;>
    by_cases h1 : 0 ≤ x 1 <;>
    by_cases h1' : x 1 < (j.1 : ℝ) + 1 <;>
    by_cases h2 : 0 ≤ x 2 <;>
    by_cases h2' : x 2 < (m : ℝ) - j.1 <;>
    simp [xr, xy, xz, h0, h1, h1', h2, h2',
      Nat.cast_sub (Nat.le_of_lt j.isLt)]

theorem cumulative_slabMeasure (x : RealGrade 1) :
    cumulative slabMeasure x = slabIndicator (x 0) := by
  classical
  by_cases h1 : 1 ≤ x 0
  · by_cases h2 : 2 ≤ x 0
    · have hnlt : ¬ x 0 < 2 := not_lt.mpr h2
      simp [slabMeasure, slabIndicator, cumulative_sub, lowerIndicator,
        lowerCoefficientHom, RealGrade.LE, h1, h2, hnlt]
    · have hlt : x 0 < 2 := lt_of_not_ge h2
      simp [slabMeasure, slabIndicator, cumulative_sub, lowerIndicator,
        lowerCoefficientHom, RealGrade.LE, h1, h2, hlt]
  · have h2 : ¬ 2 ≤ x 0 := by linarith
    simp [slabMeasure, slabIndicator, cumulative_sub, lowerIndicator,
      lowerCoefficientHom, RealGrade.LE, h1, h2]

/-! ### Proof of the staircase inversion -/

theorem pathPointNat_le_iff (m j : ℕ) (x : RealGrade 2) :
    RealGrade.LE (pathPointNat m j) x ↔
      ((j + 1 : ℕ) : ℝ) ≤ x 0 ∧ ((m - j : ℕ) : ℝ) ≤ x 1 := by
  simp [RealGrade.LE, pathPointNat, Fin.forall_fin_two]

theorem cornerPointNat_le_iff (m j : ℕ) (x : RealGrade 2) :
    RealGrade.LE (cornerPointNat m j) x ↔
      ((j + 2 : ℕ) : ℝ) ≤ x 0 ∧ ((m - j : ℕ) : ℝ) ≤ x 1 := by
  simp [RealGrade.LE, cornerPointNat, Fin.forall_fin_two]

/-- Möbius measure for the first `k` path corners of the `m`-staircase. -/
noncomputable def staircasePrefixMeasure (m k : ℕ) : AtomicSignedMeasure 2 :=
  atom ![0, 0] - (∑ j ∈ Finset.range k, atom (pathPointNat m j)) +
    ∑ j ∈ Finset.range (k - 1), atom (cornerPointNat m j)

@[simp]
theorem staircasePrefixMeasure_zero (m : ℕ) :
    staircasePrefixMeasure m 0 = atom ![0, 0] := by
  simp [staircasePrefixMeasure]

theorem staircasePrefixMeasure_one (m : ℕ) :
    staircasePrefixMeasure m 1 =
      staircasePrefixMeasure m 0 - atom (pathPointNat m 0) := by
  simp [staircasePrefixMeasure]

theorem staircasePrefixMeasure_succ_succ (m k : ℕ) :
    staircasePrefixMeasure m (k + 2) =
      staircasePrefixMeasure m (k + 1) - atom (pathPointNat m (k + 1)) +
        atom (cornerPointNat m k) := by
  have hsub : k + 2 - 1 = k + 1 := by omega
  simp only [staircasePrefixMeasure, Nat.add_sub_cancel, hsub,
    Finset.sum_range_succ]
  abel

theorem staircasePrefixMeasure_self (m : ℕ) :
    staircasePrefixMeasure m m = staircaseMeasure m := rfl

/-- Cumulative value predicted for a prefix of the staircase. -/
noncomputable def staircasePrefixValue (m k : ℕ) (x : RealGrade 2) : ℤ :=
  by
    classical
    exact if RealGrade.LE ![0, 0] x ∧
        ∀ j < k, ¬ RealGrade.LE (pathPointNat m j) x then 1 else 0

theorem pathPointNat_previous_of_below {m k : ℕ} (x : RealGrade 2)
    (hkm : k + 2 ≤ m)
    (hnew : RealGrade.LE (pathPointNat m (k + 1)) x)
    (hold : ∃ j ≤ k, RealGrade.LE (pathPointNat m j) x) :
    RealGrade.LE (pathPointNat m k) x := by
  rw [pathPointNat_le_iff] at hnew ⊢
  obtain ⟨j, hjk, hj⟩ := hold
  rw [pathPointNat_le_iff] at hj
  constructor
  · exact le_trans (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)) hnew.1
  · have hsub : m - k ≤ m - j := by omega
    exact le_trans (by exact_mod_cast hsub) hj.2

theorem cornerPointNat_below_iff {m k : ℕ} (x : RealGrade 2)
    (hkm : k + 2 ≤ m) :
    RealGrade.LE (cornerPointNat m k) x ↔
      RealGrade.LE (pathPointNat m k) x ∧
        RealGrade.LE (pathPointNat m (k + 1)) x := by
  rw [cornerPointNat_le_iff, pathPointNat_le_iff, pathPointNat_le_iff]
  have hsub : m - (k + 1) ≤ m - k := by omega
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨⟨le_trans (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)) hx, hz⟩,
      ⟨by simpa [Nat.add_assoc] using hx,
      le_trans (by exact_mod_cast hsub) hz⟩⟩
  · rintro ⟨⟨_, hz⟩, ⟨hx, _⟩⟩
    exact ⟨by simpa [Nat.add_assoc] using hx, hz⟩

theorem noPath_succ_iff (P : ℕ → Prop) (k : ℕ) :
    (∀ j < k + 1, ¬ P j) ↔ (∀ j < k, ¬ P j) ∧ ¬ P k := by
  constructor
  · intro h
    exact ⟨fun j hj ↦ h j (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ j hj
    by_cases hjk : j < k
    · exact h j hjk
    · have : j = k := by omega
      simpa [this] using hk

theorem origin_below_of_pathPointNat_below {m j : ℕ} {x : RealGrade 2}
    (h : RealGrade.LE (pathPointNat m j) x) :
    RealGrade.LE ![0, 0] x := by
  rw [pathPointNat_le_iff] at h
  rw [show RealGrade.LE ![0, 0] x ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 by
    simp [RealGrade.LE, Fin.forall_fin_two]]
  exact ⟨le_trans (by positivity) h.1, le_trans (by positivity) h.2⟩

theorem originGrade_le_iff (x : RealGrade 2) :
    RealGrade.LE ![0, 0] x ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  simp [RealGrade.LE, Fin.forall_fin_two]

/-- The cumulative formula, first for an arbitrary staircase prefix. -/
theorem cumulative_staircasePrefixMeasure (m k : ℕ) (x : RealGrade 2)
    (hkm : k ≤ m) :
    cumulative (staircasePrefixMeasure m k) x = staircasePrefixValue m k x := by
  revert hkm
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _
      by_cases ho : RealGrade.LE ![0, 0] x
      · simp [staircasePrefixValue, staircasePrefixMeasure, cumulative_atom,
          lowerIndicator, lowerCoefficientHom, ho]
      · simp [staircasePrefixValue, staircasePrefixMeasure, cumulative_atom,
          lowerIndicator, lowerCoefficientHom, ho]
  | one =>
      intro hk
      rw [staircasePrefixMeasure_one, cumulative_sub]
      simp only [staircasePrefixMeasure_zero, cumulative_atom]
      by_cases ho : RealGrade.LE ![0, 0] x
      · by_cases hp : RealGrade.LE (pathPointNat m 0) x
        · simp [staircasePrefixValue, noPath_succ_iff, ho, hp,
            lowerIndicator, lowerCoefficientHom]
        · simp [staircasePrefixValue, noPath_succ_iff, ho, hp,
            lowerIndicator, lowerCoefficientHom]
      · have hp : ¬ RealGrade.LE (pathPointNat m 0) x :=
          fun h ↦ ho (origin_below_of_pathPointNat_below h)
        simp [staircasePrefixValue, noPath_succ_iff, ho, hp,
          lowerIndicator, lowerCoefficientHom]
  | more k _ ih =>
      intro hk
      have hkprev : k + 1 ≤ m := by omega
      rw [staircasePrefixMeasure_succ_succ, cumulative_add, cumulative_sub,
        ih hkprev, cumulative_atom, cumulative_atom]
      by_cases ho : RealGrade.LE ![0, 0] x
      · by_cases hn : RealGrade.LE (pathPointNat m (k + 1)) x
        · by_cases hold : ∀ j < k + 1,
              ¬ RealGrade.LE (pathPointNat m j) x
          · have hp : ¬ RealGrade.LE (pathPointNat m k) x := by
              intro hp
              exact hold k (by omega) hp
            have hc : ¬ RealGrade.LE (cornerPointNat m k) x := by
              rw [cornerPointNat_below_iff x hk]
              tauto
            simp [staircasePrefixValue, noPath_succ_iff, ho, hn, hold, hp, hc,
              lowerIndicator, lowerCoefficientHom]
            rw [if_pos ⟨ho, hold⟩]
            norm_num
          · have hnot : ¬ ∀ j < k + 1,
                ¬ RealGrade.LE (pathPointNat m j) x := hold
            push Not at hold
            obtain ⟨j, hj, hjbelow⟩ := hold
            have hp : RealGrade.LE (pathPointNat m k) x :=
              pathPointNat_previous_of_below x hk hn ⟨j, by omega, hjbelow⟩
            have hc : RealGrade.LE (cornerPointNat m k) x :=
              (cornerPointNat_below_iff x hk).2 ⟨hp, hn⟩
            simp [staircasePrefixValue, noPath_succ_iff, ho, hn, hnot, hp, hc,
              lowerIndicator, lowerCoefficientHom]
            exact ⟨j, by omega, hjbelow⟩
        · have hc : ¬ RealGrade.LE (cornerPointNat m k) x := by
            rw [cornerPointNat_below_iff x hk]
            tauto
          have hforall : (∀ j < k + 2,
              ¬ RealGrade.LE (pathPointNat m j) x) ↔
              ∀ j < k + 1, ¬ RealGrade.LE (pathPointNat m j) x := by
            constructor
            · intro h j hj
              exact h j (by omega)
            · intro h j hj
              by_cases hjold : j < k + 1
              · exact h j hjold
              · have hjeq : j = k + 1 := by omega
                simpa [hjeq] using hn
          by_cases hold : ∀ j < k + 1,
              ¬ RealGrade.LE (pathPointNat m j) x
          · have hnew : ∀ j < k + 2,
                ¬ RealGrade.LE (pathPointNat m j) x := hforall.mpr hold
            simp [staircasePrefixValue, ho, hn, hc, hold, hnew,
              lowerIndicator, lowerCoefficientHom]
            rw [if_pos ⟨ho, hold⟩, if_pos ⟨ho, hnew⟩]
          · have hnew : ¬ ∀ j < k + 2,
                ¬ RealGrade.LE (pathPointNat m j) x :=
              fun h ↦ hold (hforall.mp h)
            simp [staircasePrefixValue, ho, hn, hc, hold, hnew,
              lowerIndicator, lowerCoefficientHom]
            push Not at hold
            obtain ⟨j, hj, hjbelow⟩ := hold
            exact ⟨j, by omega, hjbelow⟩
      · have hn : ¬ RealGrade.LE (pathPointNat m (k + 1)) x :=
          fun h ↦ ho (origin_below_of_pathPointNat_below h)
        have hc : ¬ RealGrade.LE (cornerPointNat m k) x := by
          rw [cornerPointNat_below_iff x hk]
          tauto
        simp [staircasePrefixValue, noPath_succ_iff, ho, hn, hc,
          lowerIndicator, lowerCoefficientHom]

/-- The prefix predicate at `k=m` is exactly the staircase complement `qₘ`. -/
theorem staircasePrefixValue_self (m : ℕ) (x : RealGrade 2) :
    staircasePrefixValue m m x = staircase m (x 0) (x 1) := by
  have hcond :
      (RealGrade.LE ![0, 0] x ∧
        ∀ j < m, ¬ RealGrade.LE (pathPointNat m j) x) ↔
      (0 ≤ x 0 ∧ 0 ≤ x 1 ∧
        ∀ j : Fin m,
          ¬ ((((j.1 + 1 : ℕ) : ℝ) ≤ x 0) ∧
            (((m - j.1 : ℕ) : ℝ) ≤ x 1))) := by
    rw [originGrade_le_iff]
    constructor
    · rintro ⟨⟨hy, hz⟩, h⟩
      exact ⟨hy, hz, fun j hj ↦
        h j.1 j.2 ((pathPointNat_le_iff m j.1 x).2 hj)⟩
    · rintro ⟨hy, hz, h⟩
      refine ⟨⟨hy, hz⟩, ?_⟩
      intro j hj hjbelow
      exact h ⟨j, hj⟩ ((pathPointNat_le_iff m j x).1 hjbelow)
  classical
  by_cases hleft : RealGrade.LE ![0, 0] x ∧
      ∀ j < m, ¬ RealGrade.LE (pathPointNat m j) x
  · have hright := hcond.mp hleft
    rw [staircasePrefixValue, staircase, if_pos hleft, if_pos hright]
  · have hright : ¬ (0 ≤ x 0 ∧ 0 ≤ x 1 ∧
        ∀ j : Fin m,
          ¬ ((((j.1 + 1 : ℕ) : ℝ) ≤ x 0) ∧
            (((m - j.1 : ℕ) : ℝ) ≤ x 1))) :=
      fun h ↦ hleft (hcond.mpr h)
    rw [staircasePrefixValue, staircase, if_neg hleft, if_neg hright]

/-- The cumulative function of `νₘ` is exactly the staircase complement. -/
theorem cumulative_staircaseMeasure (m : ℕ) (x : RealGrade 2) :
    cumulative (staircaseMeasure m) x = staircase m (x 0) (x 1) := by
  rw [← staircasePrefixMeasure_self]
  exact (cumulative_staircasePrefixMeasure m m x le_rfl).trans
    (staircasePrefixValue_self m x)

/-! ### The two individual ordinary-`H₀` Hilbert measures -/

/-- The always-present core component after the common vertex grade. -/
noncomputable def h0CoreMeasure : AtomicSignedMeasure 3 := atom ![0, 0, 0]

/-- One box summand for each middle vertex while both incident arms are absent. -/
noncomputable def h0DetachedMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  ∑ j : Fin m, detachedBoxMeasure m j

/-- The extra split core component before the central edge threshold and
before any two-edge path is complete. -/
noncomputable def h0SplitMeasure (m : ℕ) (threshold : ℝ) :
    AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (halfOpenIntervalMeasure 0 threshold)
    (staircaseMeasure m)

/-- Hilbert decomposition of the theta graph whose central edge appears at
the given first-coordinate threshold. -/
noncomputable def h0MeasureAtThreshold (m : ℕ) (threshold : ℝ) :
    AtomicSignedMeasure 3 :=
  h0CoreMeasure + h0DetachedMeasure m + h0SplitMeasure m threshold

noncomputable def h0FMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  h0MeasureAtThreshold m 2

noncomputable def h0GMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  h0MeasureAtThreshold m 1

theorem cumulative_h0CoreMeasure (x : RealGrade 3) :
    cumulative h0CoreMeasure x =
      if 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 then 1 else 0 := by
  classical
  have hle : RealGrade.LE (![(0 : ℝ), 0, 0] : RealGrade 3) x ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> simpa
  rw [h0CoreMeasure, cumulative_atom]
  by_cases h : 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2
  · have hgrade : RealGrade.LE (![(0 : ℝ), 0, 0] : RealGrade 3) x := hle.2 h
    simp [lowerIndicator, lowerCoefficientHom, h, hgrade]
  · have hgrade : ¬ RealGrade.LE (![(0 : ℝ), 0, 0] : RealGrade 3) x :=
      fun hx ↦ h (hle.1 hx)
    simp [lowerIndicator, lowerCoefficientHom, h, hgrade]

theorem cumulative_h0DetachedMeasure (m : ℕ) (x : RealGrade 3) :
    cumulative (h0DetachedMeasure m) x =
      ∑ j : Fin m,
        if 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 < (j.1 + 1 : ℕ) ∧
            0 ≤ x 2 ∧ x 2 < (m - j.1 : ℕ) then 1 else 0 := by
  rw [h0DetachedMeasure, cumulative_fintype_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact cumulative_detachedBoxMeasure m j x

theorem cumulative_h0DetachedMeasure_of_active (m : ℕ) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    cumulative (h0DetachedMeasure m) x =
      (Nat.card (Detached (leftAt m x) (rightAt m x)) : ℤ) := by
  classical
  have hcard :
      (Nat.card (Detached (leftAt m x) (rightAt m x)) : ℤ) =
        ∑ j : Fin m, if ¬ leftAt m x j ∧ ¬ rightAt m x j then 1 else 0 := by
    change (Nat.card {j : Fin m //
      ¬ leftAt m x j ∧ ¬ rightAt m x j} : ℤ) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa using (Finset.natCast_card_filter (R := ℤ)
      (fun j : Fin m ↦ ¬ leftAt m x j ∧ ¬ rightAt m x j) Finset.univ)
  rw [cumulative_h0DetachedMeasure, hcard]
  apply Finset.sum_congr rfl
  intro j _
  simp [leftAt, rightAt, h0, h1, h2,
    Nat.cast_sub (Nat.le_of_lt j.isLt)]
  apply if_congr
  · constructor
    · rintro ⟨hy, hz⟩
      exact ⟨hy, by linarith⟩
    · rintro ⟨hy, hz⟩
      exact ⟨hy, by linarith⟩
  · rfl
  · rfl

theorem cumulative_h0SplitMeasure (m : ℕ) (threshold : ℝ)
    (hthreshold : 0 ≤ threshold) (x : RealGrade 3) :
    cumulative (h0SplitMeasure m threshold) x =
      (if 0 ≤ x 0 ∧ x 0 < threshold then 1 else 0) *
        staircase m (x 1) (x 2) := by
  let xr : RealGrade 1 := ![x 0]
  let yz : RealGrade 2 := ![x 1, x 2]
  have hx : concatGrade xr yz = x := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [← hx]
  rw [h0SplitMeasure, cumulative_tensor,
    cumulative_halfOpenIntervalMeasure 0 threshold hthreshold,
    cumulative_staircaseMeasure]
  rfl

theorem cumulative_h0SplitMeasure_of_active (m : ℕ) (threshold : ℝ)
    (hthreshold : 0 ≤ threshold) (x : RealGrade 3)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    cumulative (h0SplitMeasure m threshold) x =
      (splitComponentExtra
        (threshold ≤ x 0 ∨ ∃ j, leftAt m x j ∧ rightAt m x j) : ℕ) := by
  classical
  rw [cumulative_h0SplitMeasure m threshold hthreshold]
  by_cases ht : threshold ≤ x 0
  · simp [h0, ht, splitComponentExtra]
  · have hxt : x 0 < threshold := lt_of_not_ge ht
    by_cases hp : ∃ j, leftAt m x j ∧ rightAt m x j
    · have hstair : staircase m (x 1) (x 2) = 0 := by
        rw [staircase, if_neg]
        rintro ⟨_, _, hnone⟩
        obtain ⟨j, hj⟩ := hp
        exact hnone j (by simpa [leftAt, rightAt] using hj)
      rw [hstair]
      simp [h0, hxt, ht, hp, splitComponentExtra]
    · have hstair : staircase m (x 1) (x 2) = 1 := by
        rw [staircase, if_pos]
        refine ⟨h1, h2, ?_⟩
        intro j hj
        exact hp ⟨j, by simpa [leftAt, rightAt] using hj⟩
      rw [hstair]
      simp [h0, hxt, ht, hp, splitComponentExtra]

theorem h0FMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (fGrade m) x : ℤ)) (h0FMeasure m) := by
  intro x
  change cumulative (h0FMeasure m) x = (ordinaryH0Dim (fGrade m) x : ℤ)
  rw [h0FMeasure, h0MeasureAtThreshold, cumulative_add, cumulative_add]
  by_cases h0 : 0 ≤ x 0 <;> by_cases h1 : 0 ≤ x 1 <;>
    by_cases h2 : 0 ≤ x 2
  · rw [cumulative_h0CoreMeasure, if_pos ⟨h0, h1, h2⟩,
      cumulative_h0DetachedMeasure_of_active m x h0 h1 h2,
      cumulative_h0SplitMeasure_of_active m 2 (by norm_num) x h0 h1 h2]
    rw [ordinaryH0Dim_fGrade_of_active m x h0 h1 h2]
    norm_num
  all_goals
    have hv : ¬ verticesActive (fGrade m) x := by
      rw [verticesActive_fGrade_iff]
      tauto
    have hdim : ordinaryH0Dim (fGrade m) x = 0 := by
      rw [ordinaryH0Dim, if_neg hv]
    rw [hdim, cumulative_h0CoreMeasure,
      cumulative_h0DetachedMeasure, cumulative_h0SplitMeasure m 2 (by norm_num)]
    simp [h0, h1, h2, staircase]

theorem h0GMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (gGrade m) x : ℤ)) (h0GMeasure m) := by
  intro x
  change cumulative (h0GMeasure m) x = (ordinaryH0Dim (gGrade m) x : ℤ)
  rw [h0GMeasure, h0MeasureAtThreshold, cumulative_add, cumulative_add]
  by_cases h0 : 0 ≤ x 0 <;> by_cases h1 : 0 ≤ x 1 <;>
    by_cases h2 : 0 ≤ x 2
  · rw [cumulative_h0CoreMeasure, if_pos ⟨h0, h1, h2⟩,
      cumulative_h0DetachedMeasure_of_active m x h0 h1 h2,
      cumulative_h0SplitMeasure_of_active m 1 (by norm_num) x h0 h1 h2]
    rw [ordinaryH0Dim_gGrade_of_active m x h0 h1 h2]
    norm_num
  all_goals
    have hv : ¬ verticesActive (gGrade m) x := by
      rw [verticesActive_gGrade_iff]
      tauto
    have hdim : ordinaryH0Dim (gGrade m) x = 0 := by
      rw [ordinaryH0Dim, if_neg hv]
    rw [hdim, cumulative_h0CoreMeasure,
      cumulative_h0DetachedMeasure, cumulative_h0SplitMeasure m 1 (by norm_num)]
    simp [h0, h1, h2, staircase]

/-! ### Identification with the graph Hilbert signed measure -/

def firstCoordinate (x : RealGrade 3) : RealGrade 1 := ![x 0]

def lastTwoCoordinates (x : RealGrade 3) : RealGrade 2 := ![x 1, x 2]

theorem concat_first_last (x : RealGrade 3) :
    concatGrade (firstCoordinate x) (lastTwoCoordinates x) = x := by
  funext i
  fin_cases i <;> rfl

/-- The product Möbius measure has precisely the graph's Hilbert-function
difference as its cumulative function. -/
theorem cumulative_hilbertDifferenceMeasure (m : ℕ) (x : RealGrade 3) :
    cumulative (hilbertDifferenceMeasure m) x = h0HilbertDifference m x := by
  rw [← concat_first_last x, hilbertDifferenceMeasure, cumulative_tensor,
    cumulative_slabMeasure, cumulative_staircaseMeasure,
    h0HilbertDifference_eq_slab_staircase]
  rfl

theorem hilbertDifferenceMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition (h0HilbertDifference m)
      (hilbertDifferenceMeasure m) :=
  cumulative_hilbertDifferenceMeasure m

/-- The finite atom formula is also an actual mathlib signed measure whose
lower-orthant values equal the ordinary-`H₀` Hilbert-function difference. -/
theorem hilbertDifferenceSignedMeasure_apply_lowerOrthant (m : ℕ)
    (x : RealGrade 3) :
    (hilbertDifferenceMeasure m).toSignedMeasure (lowerOrthant x) =
      (h0HilbertDifference m x : ℝ) := by
  rw [AtomicSignedMeasure.toSignedMeasure_apply_lowerOrthant,
    cumulative_hilbertDifferenceMeasure]

/-! ## Genuine finite Kantorovich transport -/

/-- Embed an integer lattice grade into real parameter space. -/
def Grade.toReal {n : ℕ} (a : Grade n) : RealGrade n := fun i ↦ a i

/-- Regard an integer-valued filtration as the real-valued map appearing in
the source theorem. -/
def realifyFiltration {m n : ℕ} (F : Simplex m → Grade n) :
    Simplex m → RealGrade n := fun sigma ↦ (F sigma).toReal

/-- Monotonicity for genuinely real-valued graph filtrations. -/
def RealMonotoneFiltration {m n : ℕ}
    (F : Simplex m → RealGrade n) : Prop :=
  ∀ e v, v ∈ endpoints e → RealGrade.LE (F (.vertex v)) (F (.edge e))

/-- All vertices enter at one common grade, as they do in the family `Sₘ`.
This is the hypothesis under which the fixed-vertex sublevel graph below is
literally the ordinary sublevel complex before and after the vertex grade. -/
def CommonVertexGrade {m n : ℕ}
    (F : Simplex m → RealGrade n) : Prop :=
  ∀ v, F (.vertex v) = F (.vertex (.s : Vertex m))

/-- Two filtrations agree on every simplex except possibly the distinguished
central edge `e`. -/
def OnlyCentralEdgeDiffers {m n : ℕ}
    (F G : Simplex m → RealGrade n) : Prop :=
  ∀ sigma, sigma ≠ .edge .e → F sigma = G sigma

theorem realifyFiltration_monotone {m n : ℕ} {F : Simplex m → Grade n}
    (hF : MonotoneFiltration F) : RealMonotoneFiltration (realifyFiltration F) := by
  intro e v hv i
  change ((F (.vertex v) i : ℤ) : ℝ) ≤ ((F (.edge e) i : ℤ) : ℝ)
  exact_mod_cast hF e v hv i

/-- The source theorem's finite-complex `ℓ¹` distance for real grades. -/
def realFiltrationL1Distance {m n : ℕ}
    (F G : Simplex m → RealGrade n) : ℝ :=
  ∑ sigma, realL1Distance (F sigma) (G sigma)

theorem realL1Distance_toReal {n : ℕ} (a b : Grade n) :
    realL1Distance a.toReal b.toReal = (l1Distance a b : ℝ) := by
  simp [realL1Distance, l1Distance, Grade.toReal, ← Int.cast_sub,
    ← Int.cast_abs, Nat.cast_natAbs]

theorem realFiltrationL1Distance_realify {m n : ℕ}
    (F G : Simplex m → Grade n) :
    realFiltrationL1Distance (realifyFiltration F) (realifyFiltration G) =
      (filtrationL1Distance F G : ℝ) := by
  simp [realFiltrationL1Distance, filtrationL1Distance,
    realifyFiltration, realL1Distance_toReal]

/-- Real-grade edge activation and sublevel graph, used to state the public
theorem literally with maps to `ℝⁿ`. -/
def realEdgeActive {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) (e : Edge m) : Prop := RealGrade.LE (F (.edge e)) x

def realVerticesActive {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) : Prop := RealGrade.LE (F (.vertex (.s : Vertex m))) x

/-- Every vertex of the filtered graph is present at the parameter `x`. -/
def realAllVerticesActive {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) : Prop :=
  ∀ v, RealGrade.LE (F (.vertex v)) x

theorem realAllVerticesActive_iff {m n : ℕ}
    {F : Simplex m → RealGrade n} (hcommon : CommonVertexGrade F)
    (x : RealGrade n) :
    realAllVerticesActive F x ↔ realVerticesActive F x := by
  constructor
  · intro h
    exact h .s
  · intro h v
    rw [hcommon v]
    exact h

def realSublevelGraph {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun v w ↦
    match v, w with
    | .s, .t => realEdgeActive F x .e
    | .s, .u j => realEdgeActive F x (.a j)
    | .u j, .t => realEdgeActive F x (.b j)
    | _, _ => False

/-- The hard-coded sublevel adjacency is carried by the concrete graph
`graph m`; no extra edge can appear. -/
theorem realSublevelGraph_le_graph {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    realSublevelGraph F x ≤ graph m := by
  intro v w hvw
  cases v with
  | s =>
      cases w with
      | s => exact (hvw.ne rfl).elim
      | t =>
          exact ⟨by simp,
            Or.inl ⟨(.e : Edge m), by simp [endpoints]⟩⟩
      | u j =>
          exact ⟨by simp,
            Or.inl ⟨(.a j : Edge m), by simp [endpoints]⟩⟩
  | t =>
      cases w with
      | s =>
          exact ⟨by simp,
            Or.inr ⟨(.e : Edge m), by simp [endpoints]⟩⟩
      | t => exact (hvw.ne rfl).elim
      | u j =>
          exact ⟨by simp,
            Or.inr ⟨(.b j : Edge m), by simp [endpoints]⟩⟩
  | u i =>
      cases w with
      | s =>
          exact ⟨by simp,
            Or.inr ⟨(.a i : Edge m), by simp [endpoints]⟩⟩
      | t =>
          exact ⟨by simp,
            Or.inl ⟨(.b i : Edge m), by simp [endpoints]⟩⟩
      | u j =>
          exact (by simpa [realSublevelGraph] using hvw : False).elim

noncomputable def realOrdinaryH0Dim {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) : ℕ := by
  classical
  exact if realVerticesActive F x then
    Nat.card (realSublevelGraph F x).ConnectedComponent else 0

@[simp]
theorem realVerticesActive_realify {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) :
    realVerticesActive (realifyFiltration F) x = verticesActive F x := rfl

@[simp]
theorem realSublevelGraph_realify {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) :
    realSublevelGraph (realifyFiltration F) x = sublevelGraph F x := rfl

@[simp]
theorem realOrdinaryH0Dim_realify {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) :
    realOrdinaryH0Dim (realifyFiltration F) x = ordinaryH0Dim F x := rfl

@[simp]
theorem Grade.toReal_zero_two :
    Grade.toReal (![(0 : ℤ), 0] : Grade 2) = (![0, 0] : RealGrade 2) := by
  funext i
  fin_cases i <;> simp [Grade.toReal]

/-- Distinct integer-lattice points are at `ℓ¹` distance at least one. -/
theorem one_le_realL1Distance_toReal_of_ne {n : ℕ} {a b : Grade n}
    (h : a ≠ b) : 1 ≤ realL1Distance a.toReal b.toReal := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hsub : a i - b i ≠ 0 := sub_ne_zero.mpr hi
  have hint : (1 : ℤ) ≤ |a i - b i| := Int.one_le_abs hsub
  have hreal : (1 : ℝ) ≤ |(a i : ℝ) - (b i : ℝ)| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast hint
  exact hreal.trans <| Finset.single_le_sum
    (fun j _ ↦ abs_nonneg ((a j : ℝ) - (b j : ℝ))) (Finset.mem_univ i)

/-- Integer versions of the negative staircase atoms. -/
def pathPointInteger (m j : ℕ) : Grade 2 :=
  ![((j + 1 : ℕ) : ℤ), ((m - j : ℕ) : ℤ)]

/-- Integer versions of the non-origin positive staircase atoms. -/
def cornerPointInteger (m j : ℕ) : Grade 2 :=
  ![((j + 2 : ℕ) : ℤ), ((m - j : ℕ) : ℤ)]

/-- Index set for the `m` positive atoms of `νₘ`: the origin and the
`m-1` adjacent corners. -/
abbrev StaircasePositiveIndex (m : ℕ) := Unit ⊕ Fin (m - 1)

def staircasePositiveInteger (m : ℕ) : StaircasePositiveIndex m → Grade 2
  | .inl _ => ![0, 0]
  | .inr j => cornerPointInteger m j.1

def staircaseNegativeInteger (m : ℕ) (j : Fin m) : Grade 2 :=
  pathPointInteger m j.1

theorem staircasePositiveInteger_ne_negativeInteger {m : ℕ} (hm : 1 ≤ m)
    (i : StaircasePositiveIndex m) (j : Fin m) :
    staircasePositiveInteger m i ≠ staircaseNegativeInteger m j := by
  intro h
  cases i with
  | inl u =>
      have h0 := congrFun h (0 : Fin 2)
      simp [staircasePositiveInteger, staircaseNegativeInteger,
        pathPointInteger] at h0
      have hpos : (0 : ℤ) < (j.1 : ℤ) + 1 := by positivity
      omega
  | inr k =>
      have h0 := congrFun h (0 : Fin 2)
      have h1 := congrFun h (1 : Fin 2)
      simp [staircasePositiveInteger, staircaseNegativeInteger,
        pathPointInteger, cornerPointInteger] at h0 h1
      have hk : k.1 + 2 ≤ m := by omega
      omega

/-- Add the slab coordinate to a two-dimensional integer grade. -/
def prependInteger (r : ℤ) (a : Grade 2) : Grade 3 := ![r, a 0, a 1]

/-- Common index set for the `2m` positive and `2m` negative atoms of
`Δₘ`; the left summand indexes positive staircase atoms. -/
abbrev CounterexampleAtomIndex (m : ℕ) := StaircasePositiveIndex m ⊕ Fin m

/-- Positive atoms of the Hilbert signed-measure difference. -/
def counterexampleSourceInteger (m : ℕ) : CounterexampleAtomIndex m → Grade 3
  | .inl i => prependInteger 1 (staircasePositiveInteger m i)
  | .inr j => prependInteger 2 (staircaseNegativeInteger m j)

/-- Negative atoms of the Hilbert signed-measure difference. -/
def counterexampleTargetInteger (m : ℕ) : CounterexampleAtomIndex m → Grade 3
  | .inl i => prependInteger 2 (staircasePositiveInteger m i)
  | .inr j => prependInteger 1 (staircaseNegativeInteger m j)

def counterexampleSourcePoint (m : ℕ) (i : CounterexampleAtomIndex m) :
    RealGrade 3 := (counterexampleSourceInteger m i).toReal

def counterexampleTargetPoint (m : ℕ) (i : CounterexampleAtomIndex m) :
    RealGrade 3 := (counterexampleTargetInteger m i).toReal

theorem counterexampleSourceInteger_ne_targetInteger {m : ℕ} (hm : 1 ≤ m)
    (i j : CounterexampleAtomIndex m) :
    counterexampleSourceInteger m i ≠ counterexampleTargetInteger m j := by
  intro h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleSourceInteger, counterexampleTargetInteger,
            prependInteger] at h0
      | inr j =>
          apply staircasePositiveInteger_ne_negativeInteger hm i j
          funext q
          fin_cases q
          · exact congrFun h (1 : Fin 3)
          · exact congrFun h (2 : Fin 3)
  | inr i =>
      cases j with
      | inl j =>
          apply staircasePositiveInteger_ne_negativeInteger hm j i
          funext q
          fin_cases q
          · exact (congrFun h (1 : Fin 3)).symm
          · exact (congrFun h (2 : Fin 3)).symm
      | inr j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleSourceInteger, counterexampleTargetInteger,
            prependInteger] at h0

theorem one_le_counterexample_source_target_distance {m : ℕ} (hm : 1 ≤ m)
    (i j : CounterexampleAtomIndex m) :
    1 ≤ realL1Distance (counterexampleSourcePoint m i)
      (counterexampleTargetPoint m j) :=
  one_le_realL1Distance_toReal_of_ne
    (counterexampleSourceInteger_ne_targetInteger hm i j)

theorem counterexample_corresponding_distance (m : ℕ)
    (i : CounterexampleAtomIndex m) :
    realL1Distance (counterexampleSourcePoint m i)
      (counterexampleTargetPoint m i) = 1 := by
  cases i <;>
    simp [counterexampleSourcePoint, counterexampleTargetPoint,
      counterexampleSourceInteger, counterexampleTargetInteger,
      Grade.toReal, prependInteger, realL1Distance, Fin.sum_univ_succ] <;>
    norm_num

theorem card_counterexampleAtomIndex {m : ℕ} (hm : 1 ≤ m) :
    Fintype.card (CounterexampleAtomIndex m) = 2 * m := by
  simp [CounterexampleAtomIndex, StaircasePositiveIndex]
  omega

/-- A genuine nonnegative coupling between two equally indexed families of
unit atoms.  Row and column equations are the marginal constraints. -/
structure UnitCoupling {n : ℕ} {I : Type*} [Fintype I]
    (source target : I → RealGrade n) where
  mass : I → I → ℝ
  nonnegative : ∀ i j, 0 ≤ mass i j
  row_sum : ∀ i, ∑ j, mass i j = 1
  column_sum : ∀ j, ∑ i, mass i j = 1

def UnitCoupling.cost {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n} (c : UnitCoupling source target) : ℝ :=
  ∑ i, ∑ j, c.mass i j * realL1Distance (source i) (target j)

noncomputable def identityUnitCoupling {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (source target : I → RealGrade n) :
    UnitCoupling source target where
  mass i j := if i = j then 1 else 0
  nonnegative i j := by positivity
  row_sum i := by simp
  column_sum j := by simp

theorem identityUnitCoupling_cost {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (source target : I → RealGrade n) :
    (identityUnitCoupling source target).cost =
      ∑ i, realL1Distance (source i) (target i) := by
  simp [UnitCoupling.cost, identityUnitCoupling]

theorem UnitCoupling.cost_nonnegative {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n} (c : UnitCoupling source target) :
    0 ≤ c.cost := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (c.nonnegative i j)
  apply Finset.sum_nonneg
  intro q _
  exact abs_nonneg _

theorem UnitCoupling.card_le_cost {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n} (c : UnitCoupling source target)
    (hdistance : ∀ i j, 1 ≤ realL1Distance (source i) (target j)) :
    (Fintype.card I : ℝ) ≤ c.cost := by
  calc
    (Fintype.card I : ℝ) = ∑ i : I, (1 : ℝ) := by simp
    _ = ∑ i : I, ∑ j : I, c.mass i j := by
      congr 1
      funext i
      exact (c.row_sum i).symm
    _ ≤ ∑ i : I, ∑ j : I,
        c.mass i j * realL1Distance (source i) (target j) := by
      gcongr with i j
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hdistance i j) (c.nonnegative i j)
    _ = c.cost := rfl

/-- `KR₁` for two finite unit atomic measures: the infimum over all genuine
couplings with the `ℓ¹` ground cost. -/
noncomputable def unitAtomicKR1 {n : ℕ} {I : Type*} [Fintype I]
    (source target : I → RealGrade n) : ℝ :=
  sInf {r | ∃ c : UnitCoupling source target, c.cost = r}

theorem unitAtomicKR1_eq_card_of_separated_unit_matching {n : ℕ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (source target : I → RealGrade n)
    (hsep : ∀ i j, 1 ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = 1) :
    unitAtomicKR1 source target = Fintype.card I := by
  let c₀ := identityUnitCoupling source target
  have hcost : c₀.cost = Fintype.card I := by
    rw [identityUnitCoupling_cost]
    simp [hmatch]
  have hbounded : BddBelow {r | ∃ c : UnitCoupling source target, c.cost = r} := by
    refine ⟨0, ?_⟩
    intro r hr
    obtain ⟨c, rfl⟩ := hr
    exact c.cost_nonnegative
  apply le_antisymm
  · exact csInf_le hbounded ⟨c₀, hcost⟩
  · apply le_csInf
    · exact ⟨c₀.cost, c₀, rfl⟩
    · intro r hr
      obtain ⟨c, rfl⟩ := hr
      exact c.card_le_cost hsep

/-- Exact transport cost for the positive and negative atoms of `Δₘ`. -/
theorem counterexample_unitAtomicKR1 (m : ℕ) (hm : 1 ≤ m) :
    unitAtomicKR1 (counterexampleSourcePoint m) (counterexampleTargetPoint m) =
      2 * m := by
  rw [unitAtomicKR1_eq_card_of_separated_unit_matching
    _ _ (one_le_counterexample_source_target_distance hm)
    (counterexample_corresponding_distance m), card_counterexampleAtomIndex hm]
  norm_num

/-! ### Positive and negative atoms are the Jordan parts -/

noncomputable def staircasePositiveMeasure (m : ℕ) : AtomicSignedMeasure 2 :=
  atom ![0, 0] + ∑ j ∈ Finset.range (m - 1), atom (cornerPointNat m j)

noncomputable def staircaseNegativeMeasure (m : ℕ) : AtomicSignedMeasure 2 :=
  ∑ j ∈ Finset.range m, atom (pathPointNat m j)

theorem staircaseMeasure_eq_positive_sub_negative (m : ℕ) :
    staircaseMeasure m =
      staircasePositiveMeasure m - staircaseNegativeMeasure m := by
  simp only [staircaseMeasure, staircasePositiveMeasure, staircaseNegativeMeasure]
  abel

theorem AtomicSignedMeasure.tensor_zero_left {n k : ℕ}
    (nu : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor (0 : AtomicSignedMeasure n) nu = 0 := by
  classical
  simp [AtomicSignedMeasure.tensor]

theorem AtomicSignedMeasure.tensor_zero_right {n k : ℕ}
    (mu : AtomicSignedMeasure n) :
    AtomicSignedMeasure.tensor mu (0 : AtomicSignedMeasure k) = 0 := by
  classical
  simp [AtomicSignedMeasure.tensor]

theorem AtomicSignedMeasure.tensor_neg_left {n k : ℕ}
    (mu : AtomicSignedMeasure n) (nu : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor (-mu) nu = -AtomicSignedMeasure.tensor mu nu := by
  have h : AtomicSignedMeasure.tensor mu nu +
      AtomicSignedMeasure.tensor (-mu) nu = 0 := by
    rw [← AtomicSignedMeasure.tensor_add_left]
    simp [AtomicSignedMeasure.tensor_zero_left]
  exact eq_neg_of_add_eq_zero_right h

theorem AtomicSignedMeasure.tensor_neg_right {n k : ℕ}
    (mu : AtomicSignedMeasure n) (nu : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor mu (-nu) = -AtomicSignedMeasure.tensor mu nu := by
  have h : AtomicSignedMeasure.tensor mu nu +
      AtomicSignedMeasure.tensor mu (-nu) = 0 := by
    rw [← AtomicSignedMeasure.tensor_add_right]
    simp [AtomicSignedMeasure.tensor_zero_right]
  exact eq_neg_of_add_eq_zero_right h

theorem AtomicSignedMeasure.tensor_sub_left {n k : ℕ}
    (mu₁ mu₂ : AtomicSignedMeasure n) (nu : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor (mu₁ - mu₂) nu =
      AtomicSignedMeasure.tensor mu₁ nu - AtomicSignedMeasure.tensor mu₂ nu := by
  simp [sub_eq_add_neg, AtomicSignedMeasure.tensor_add_left,
    AtomicSignedMeasure.tensor_neg_left]

theorem AtomicSignedMeasure.tensor_sub_right {n k : ℕ}
    (mu : AtomicSignedMeasure n) (nu₁ nu₂ : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor mu (nu₁ - nu₂) =
      AtomicSignedMeasure.tensor mu nu₁ - AtomicSignedMeasure.tensor mu nu₂ := by
  simp [sub_eq_add_neg, AtomicSignedMeasure.tensor_add_right,
    AtomicSignedMeasure.tensor_neg_right]

theorem AtomicSignedMeasure.tensor_atom_atom {n k : ℕ}
    (a : RealGrade n) (b : RealGrade k) :
    AtomicSignedMeasure.tensor (atom a) (atom b) = atom (concatGrade a b) := by
  simpa [atom] using AtomicSignedMeasure.tensor_single_single a 1 b 1

theorem AtomicSignedMeasure.tensor_fintype_sum_right {n k : ℕ}
    {I : Type*} [Fintype I] (mu : AtomicSignedMeasure n)
    (nu : I → AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor mu (∑ i, nu i) =
      ∑ i, AtomicSignedMeasure.tensor mu (nu i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [AtomicSignedMeasure.tensor_zero_right]
  | @insert i s hi ih =>
      simp [hi, AtomicSignedMeasure.tensor_add_right, ih]

theorem AtomicSignedMeasure.tensor_finset_sum_right {n k : ℕ}
    {I : Type*} (s : Finset I) (mu : AtomicSignedMeasure n)
    (nu : I → AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor mu (∑ i ∈ s, nu i) =
      ∑ i ∈ s, AtomicSignedMeasure.tensor mu (nu i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AtomicSignedMeasure.tensor_zero_right]
  | @insert i s hi ih =>
      simp [hi, AtomicSignedMeasure.tensor_add_right, ih]

/-- Positive part displayed in equation (5). -/
noncomputable def counterexamplePositiveMeasure (m : ℕ) :
    AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (atom ![1]) (staircasePositiveMeasure m) +
    AtomicSignedMeasure.tensor (atom ![2]) (staircaseNegativeMeasure m)

/-- Negative part displayed in equation (5). -/
noncomputable def counterexampleNegativeMeasure (m : ℕ) :
    AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (atom ![1]) (staircaseNegativeMeasure m) +
    AtomicSignedMeasure.tensor (atom ![2]) (staircasePositiveMeasure m)

theorem hilbertDifferenceMeasure_eq_positive_sub_negative (m : ℕ) :
    hilbertDifferenceMeasure m =
      counterexamplePositiveMeasure m - counterexampleNegativeMeasure m := by
  rw [hilbertDifferenceMeasure, slabMeasure,
    staircaseMeasure_eq_positive_sub_negative,
    AtomicSignedMeasure.tensor_sub_left,
    AtomicSignedMeasure.tensor_sub_right,
    AtomicSignedMeasure.tensor_sub_right]
  simp only [counterexamplePositiveMeasure, counterexampleNegativeMeasure]
  abel

theorem pathPointInteger_toReal (m j : ℕ) :
    (pathPointInteger m j).toReal = pathPointNat m j := by
  funext i
  fin_cases i <;> rfl

theorem cornerPointInteger_toReal (m j : ℕ) :
    (cornerPointInteger m j).toReal = cornerPointNat m j := by
  funext i
  fin_cases i <;> rfl

theorem prependInteger_toReal (r : ℤ) (a : Grade 2) :
    (prependInteger r a).toReal = concatGrade ![(r : ℝ)] a.toReal := by
  funext i
  fin_cases i <;> rfl

theorem sum_counterexampleSourcePoint_atoms (m : ℕ) :
    (∑ i : CounterexampleAtomIndex m, atom (counterexampleSourcePoint m i)) =
      counterexamplePositiveMeasure m := by
  classical
  have hcorner :
      (∑ j : Fin (m - 1),
        atom (counterexampleSourcePoint m (.inl (.inr j)))) =
      ∑ j ∈ Finset.range (m - 1),
        atom (concatGrade ![1] (cornerPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, counterexampleSourcePoint,
      counterexampleSourceInteger, staircasePositiveInteger,
      prependInteger_toReal, cornerPointInteger_toReal]
  have hpath :
      (∑ j : Fin m, atom (counterexampleSourcePoint m (.inr j))) =
      ∑ j ∈ Finset.range m,
        atom (concatGrade ![2] (pathPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, counterexampleSourcePoint,
      counterexampleSourceInteger, staircaseNegativeInteger,
      prependInteger_toReal, pathPointInteger_toReal]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hcorner, hpath]
  simp only [counterexamplePositiveMeasure, staircasePositiveMeasure,
    staircaseNegativeMeasure, AtomicSignedMeasure.tensor_add_right,
    AtomicSignedMeasure.tensor_finset_sum_right,
    AtomicSignedMeasure.tensor_atom_atom]
  simp [counterexampleSourcePoint, counterexampleSourceInteger,
    staircasePositiveInteger, prependInteger_toReal, Grade.toReal]

theorem sum_counterexampleTargetPoint_atoms (m : ℕ) :
    (∑ i : CounterexampleAtomIndex m, atom (counterexampleTargetPoint m i)) =
      counterexampleNegativeMeasure m := by
  classical
  have hcorner :
      (∑ j : Fin (m - 1),
        atom (counterexampleTargetPoint m (.inl (.inr j)))) =
      ∑ j ∈ Finset.range (m - 1),
        atom (concatGrade ![2] (cornerPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, counterexampleTargetPoint,
      counterexampleTargetInteger, staircasePositiveInteger,
      prependInteger_toReal, cornerPointInteger_toReal]
  have hpath :
      (∑ j : Fin m, atom (counterexampleTargetPoint m (.inr j))) =
      ∑ j ∈ Finset.range m,
        atom (concatGrade ![1] (pathPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, counterexampleTargetPoint,
      counterexampleTargetInteger, staircaseNegativeInteger,
      prependInteger_toReal, pathPointInteger_toReal]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hcorner, hpath]
  simp only [counterexampleNegativeMeasure, staircasePositiveMeasure,
    staircaseNegativeMeasure, AtomicSignedMeasure.tensor_add_right,
    AtomicSignedMeasure.tensor_finset_sum_right,
    AtomicSignedMeasure.tensor_atom_atom]
  simp [counterexampleTargetPoint, counterexampleTargetInteger,
    staircasePositiveInteger, prependInteger_toReal, Grade.toReal, add_comm]

/-- Coefficient-level identification of the exact positive and negative atom
families used by the transport problem. -/
theorem hilbertDifferenceMeasure_eq_indexed_jordan (m : ℕ) :
    hilbertDifferenceMeasure m =
      (∑ i : CounterexampleAtomIndex m, atom (counterexampleSourcePoint m i)) -
        ∑ i : CounterexampleAtomIndex m, atom (counterexampleTargetPoint m i) := by
  rw [sum_counterexampleSourcePoint_atoms, sum_counterexampleTargetPoint_atoms,
    hilbertDifferenceMeasure_eq_positive_sub_negative]

theorem Grade.toReal_injective {n : ℕ} :
    Function.Injective (@Grade.toReal n) := by
  intro a b h
  funext i
  have hi := congrFun h i
  change (a i : ℝ) = (b i : ℝ) at hi
  exact Int.cast_injective hi

theorem staircasePositiveInteger_injective (m : ℕ) :
    Function.Injective (staircasePositiveInteger m) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => cases i; cases j; rfl
      | inr j =>
          have h0 := congrFun h (0 : Fin 2)
          simp [staircasePositiveInteger, cornerPointInteger] at h0
          have hpos : (0 : ℤ) < (j.1 : ℤ) + 2 := by positivity
          omega
  | inr i =>
      cases j with
      | inl j =>
          have h0 := congrFun h (0 : Fin 2)
          simp [staircasePositiveInteger, cornerPointInteger] at h0
          have hpos : (0 : ℤ) < (i.1 : ℤ) + 2 := by positivity
          omega
      | inr j =>
          have hij : i = j := by
            apply Fin.ext
            have h0 := congrFun h (0 : Fin 2)
            simp [staircasePositiveInteger, cornerPointInteger] at h0
            omega
          subst j
          rfl

theorem staircaseNegativeInteger_injective (m : ℕ) :
    Function.Injective (staircaseNegativeInteger m) := by
  intro i j h
  apply Fin.ext
  have h0 := congrFun h (0 : Fin 2)
  simp [staircaseNegativeInteger, pathPointInteger] at h0
  omega

theorem counterexampleSourceInteger_injective (m : ℕ) :
    Function.Injective (counterexampleSourceInteger m) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hij : i = j := staircasePositiveInteger_injective m <| by
            funext q
            fin_cases q
            · exact congrFun h (1 : Fin 3)
            · exact congrFun h (2 : Fin 3)
          subst j
          rfl
      | inr j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleSourceInteger, prependInteger] at h0
  | inr i =>
      cases j with
      | inl j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleSourceInteger, prependInteger] at h0
      | inr j =>
          have hij : i = j := staircaseNegativeInteger_injective m <| by
            funext q
            fin_cases q
            · exact congrFun h (1 : Fin 3)
            · exact congrFun h (2 : Fin 3)
          subst j
          rfl

theorem counterexampleTargetInteger_injective (m : ℕ) :
    Function.Injective (counterexampleTargetInteger m) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hij : i = j := staircasePositiveInteger_injective m <| by
            funext q
            fin_cases q
            · exact congrFun h (1 : Fin 3)
            · exact congrFun h (2 : Fin 3)
          subst j
          rfl
      | inr j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleTargetInteger, prependInteger] at h0
  | inr i =>
      cases j with
      | inl j =>
          have h0 := congrFun h (0 : Fin 3)
          norm_num [counterexampleTargetInteger, prependInteger] at h0
      | inr j =>
          have hij : i = j := staircaseNegativeInteger_injective m <| by
            funext q
            fin_cases q
            · exact congrFun h (1 : Fin 3)
            · exact congrFun h (2 : Fin 3)
          subst j
          rfl

theorem counterexampleSourcePoint_injective (m : ℕ) :
    Function.Injective (counterexampleSourcePoint m) :=
  Grade.toReal_injective.comp (counterexampleSourceInteger_injective m)

theorem counterexampleTargetPoint_injective (m : ℕ) :
    Function.Injective (counterexampleTargetPoint m) :=
  Grade.toReal_injective.comp (counterexampleTargetInteger_injective m)

theorem counterexampleSourcePoint_ne_targetPoint {m : ℕ} (hm : 1 ≤ m)
    (i j : CounterexampleAtomIndex m) :
    counterexampleSourcePoint m i ≠ counterexampleTargetPoint m j := by
  intro h
  exact counterexampleSourceInteger_ne_targetInteger hm i j
    (Grade.toReal_injective h)

/-- A certificate that a signed atomic measure is written as its disjoint
positive and negative unit atoms.  Injectivity excludes multiplicities and
cross-disjointness excludes cancellation, so these are its Jordan parts. -/
def IsUnitAtomicJordanRepresentation {n : ℕ} {I : Type*} [Fintype I]
    (mu : AtomicSignedMeasure n) (source target : I → RealGrade n) : Prop :=
  Function.Injective source ∧ Function.Injective target ∧
    (∀ i j, source i ≠ target j) ∧
    mu = (∑ i, atom (source i)) - ∑ j, atom (target j)

/-- The genuine positive measure carried by a finite family of unit atoms. -/
noncomputable def unitAtomMeasure {n : ℕ} {I : Type*} [Fintype I]
    (points : I → RealGrade n) : Measure (RealGrade n) :=
  ∑ i, Measure.dirac (points i)

noncomputable instance isFiniteMeasure_unitAtomMeasure {n : ℕ}
    {I : Type*} [Fintype I] (points : I → RealGrade n) :
    IsFiniteMeasure (unitAtomMeasure points) := by
  unfold unitAtomMeasure
  infer_instance

theorem AtomicSignedMeasure.toSignedMeasure_finset_sum {n : ℕ}
    {I : Type*} (s : Finset I) (mu : I → AtomicSignedMeasure n) :
    (∑ i ∈ s, mu i).toSignedMeasure = ∑ i ∈ s, (mu i).toSignedMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AtomicSignedMeasure.toSignedMeasure]
  | @insert i s hi ih =>
      simp [hi, AtomicSignedMeasure.toSignedMeasure_add, ih]

theorem AtomicSignedMeasure.toSignedMeasure_fintype_sum {n : ℕ}
    {I : Type*} [Fintype I] (mu : I → AtomicSignedMeasure n) :
    (∑ i, mu i).toSignedMeasure = ∑ i, (mu i).toSignedMeasure := by
  classical
  simpa using AtomicSignedMeasure.toSignedMeasure_finset_sum Finset.univ mu

theorem Measure.toSignedMeasure_finset_sum {X I : Type*} [MeasurableSpace X]
    (s : Finset I) (mu : I → Measure X) [∀ i, IsFiniteMeasure (mu i)] :
    (∑ i ∈ s, mu i).toSignedMeasure = ∑ i ∈ s, (mu i).toSignedMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem Measure.toSignedMeasure_fintype_sum {X I : Type*} [MeasurableSpace X]
    [Fintype I] (mu : I → Measure X) [∀ i, IsFiniteMeasure (mu i)] :
    (∑ i, mu i).toSignedMeasure = ∑ i, (mu i).toSignedMeasure := by
  classical
  simpa using Measure.toSignedMeasure_finset_sum Finset.univ mu

/-- The coefficient-level sum of unit atoms realizes exactly the corresponding
finite sum of mathlib Dirac measures. -/
theorem unitAtomMeasure_toSignedMeasure {n : ℕ} {I : Type*} [Fintype I]
    (points : I → RealGrade n) :
    (unitAtomMeasure points).toSignedMeasure =
      (∑ i, atom (points i)).toSignedMeasure := by
  classical
  change (∑ i, Measure.dirac (points i)).toSignedMeasure =
    (∑ i, atom (points i)).toSignedMeasure
  rw [Measure.toSignedMeasure_fintype_sum,
    AtomicSignedMeasure.toSignedMeasure_fintype_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [atom, AtomicSignedMeasure.toSignedMeasure]

/-- Disjoint finite point supports give mutually singular positive measures. -/
theorem unitAtomMeasure_mutuallySingular {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n} (hcross : ∀ i j, source i ≠ target j) :
    unitAtomMeasure source ⟂ₘ unitAtomMeasure target := by
  classical
  let S : Set (RealGrade n) := Set.range source
  have hS : MeasurableSet S := Set.toFinite S |>.measurableSet
  refine ⟨Sᶜ, hS.compl, ?_, ?_⟩
  · simp [unitAtomMeasure, Finset.sum_apply, hS.compl, S]
  · rw [compl_compl]
    change (∑ j : I, Measure.dirac (target j)) S = 0
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [Measure.dirac_apply' _ hS]
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [if_neg]
    rintro ⟨i, hi⟩
    exact hcross i j hi

/-- The actual mathlib Jordan decomposition associated with disjoint unit
source and target atoms. -/
noncomputable def unitAtomicJordanDecomposition {n : ℕ} {I : Type*}
    [Fintype I] (source target : I → RealGrade n)
    (hcross : ∀ i j, source i ≠ target j) :
    MeasureTheory.JordanDecomposition (RealGrade n) where
  posPart := unitAtomMeasure source
  negPart := unitAtomMeasure target
  mutuallySingular := unitAtomMeasure_mutuallySingular hcross

/-- A unit-atom Jordan certificate identifies the positive and negative
families with mathlib's unique Jordan decomposition of the genuine signed
Dirac measure. -/
theorem IsUnitAtomicJordanRepresentation.toJordanDecomposition {n : ℕ}
    {I : Type*} [Fintype I] {mu : AtomicSignedMeasure n}
    {source target : I → RealGrade n}
    (h : IsUnitAtomicJordanRepresentation mu source target) :
    mu.toSignedMeasure.toJordanDecomposition =
      unitAtomicJordanDecomposition source target h.2.2.1 := by
  apply SignedMeasure.toJordanDecomposition_eq
  calc
    mu.toSignedMeasure =
        ((∑ i, atom (source i)) - ∑ j, atom (target j)).toSignedMeasure :=
      congrArg AtomicSignedMeasure.toSignedMeasure h.2.2.2
    _ = (∑ i, atom (source i)).toSignedMeasure -
        (∑ j, atom (target j)).toSignedMeasure :=
      AtomicSignedMeasure.toSignedMeasure_sub _ _
    _ = (unitAtomicJordanDecomposition source target h.2.2.1).toSignedMeasure := by
      rw [← unitAtomMeasure_toSignedMeasure source,
        ← unitAtomMeasure_toSignedMeasure target]
      rfl

theorem IsUnitAtomicJordanRepresentation.posPart_eq_unitAtomMeasure {n : ℕ}
    {I : Type*} [Fintype I] {mu : AtomicSignedMeasure n}
    {source target : I → RealGrade n}
    (h : IsUnitAtomicJordanRepresentation mu source target) :
    mu.toSignedMeasure.toJordanDecomposition.posPart = unitAtomMeasure source := by
  rw [h.toJordanDecomposition]
  rfl

theorem IsUnitAtomicJordanRepresentation.negPart_eq_unitAtomMeasure {n : ℕ}
    {I : Type*} [Fintype I] {mu : AtomicSignedMeasure n}
    {source target : I → RealGrade n}
    (h : IsUnitAtomicJordanRepresentation mu source target) :
    mu.toSignedMeasure.toJordanDecomposition.negPart = unitAtomMeasure target := by
  rw [h.toJordanDecomposition]
  rfl

/-! ### The published measure-coupling definition of `KR₁` -/

/-- A genuine measure on the product with prescribed first and second
marginals.  The marginal equations are stated on all measurable sets, so
this is exactly a transport plan in `Π(mu,nu)`. -/
structure L1MeasureCoupling {n : ℕ}
    (mu nu : Measure (RealGrade n)) where
  plan : Measure (RealGrade n × RealGrade n)
  fst_marginal : ∀ s, MeasurableSet s →
    plan (Prod.fst ⁻¹' s) = mu s
  snd_marginal : ∀ s, MeasurableSet s →
    plan (Prod.snd ⁻¹' s) = nu s

/-- The actual `ℓ¹`-transport integral of a measure coupling. -/
noncomputable def L1MeasureCoupling.cost {n : ℕ}
    {mu nu : Measure (RealGrade n)} (c : L1MeasureCoupling mu nu) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (realL1Distance z.1 z.2) ∂c.plan

/-- The matching `i ↦ i` as an actual finite measure on the product. -/
noncomputable def matchingMeasureCoupling {n : ℕ} {I : Type*}
    [Fintype I] (source target : I → RealGrade n) :
    L1MeasureCoupling (unitAtomMeasure source) (unitAtomMeasure target) where
  plan := ∑ i, Measure.dirac (source i, target i)
  fst_marginal s hs := by
    classical
    simp [unitAtomMeasure, Measure.finsetSum_apply, hs,
      hs.preimage measurable_fst]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  snd_marginal s hs := by
    classical
    simp [unitAtomMeasure, Measure.finsetSum_apply, hs,
      hs.preimage measurable_snd]
    apply Finset.sum_congr rfl
    intro i _
    rfl

theorem unitAtomMeasure_compl_range {n : ℕ} {I : Type*}
    [Fintype I] (points : I → RealGrade n) :
    unitAtomMeasure points (Set.range points)ᶜ = 0 := by
  classical
  let S : Set (RealGrade n) := Set.range points
  have hS : MeasurableSet S := Set.toFinite S |>.measurableSet
  simp [unitAtomMeasure, Measure.finsetSum_apply, hS.compl, S]

theorem L1MeasureCoupling.totalMass_unitAtoms {n : ℕ}
    {I : Type*} [Fintype I] {source target : I → RealGrade n}
    (c : L1MeasureCoupling (unitAtomMeasure source) (unitAtomMeasure target)) :
    c.plan Set.univ = Fintype.card I := by
  calc
    c.plan Set.univ = unitAtomMeasure source Set.univ := by
      simpa using c.fst_marginal Set.univ MeasurableSet.univ
    _ = Fintype.card I := by simp [unitAtomMeasure]

/-- The measure-theoretic lower certificate: the marginal equations force
the plan to be supported on the finite source-target product, where every
unit of mass travels at least one. -/
theorem L1MeasureCoupling.card_le_cost_of_separated {n : ℕ}
    {I : Type*} [Fintype I] {source target : I → RealGrade n}
    (c : L1MeasureCoupling (unitAtomMeasure source) (unitAtomMeasure target))
    (hsep : ∀ i j, 1 ≤ realL1Distance (source i) (target j)) :
    (Fintype.card I : ℝ≥0∞) ≤ c.cost := by
  let S : Set (RealGrade n) := Set.range source
  let T : Set (RealGrade n) := Set.range target
  have hS : MeasurableSet S := Set.toFinite S |>.measurableSet
  have hT : MeasurableSet T := Set.toFinite T |>.measurableSet
  have hfst : ∀ᵐ z ∂c.plan, z.1 ∈ S := by
    rw [ae_iff]
    change c.plan (Prod.fst ⁻¹' Sᶜ) = 0
    rw [c.fst_marginal Sᶜ hS.compl]
    exact unitAtomMeasure_compl_range source
  have hsnd : ∀ᵐ z ∂c.plan, z.2 ∈ T := by
    rw [ae_iff]
    change c.plan (Prod.snd ⁻¹' Tᶜ) = 0
    rw [c.snd_marginal Tᶜ hT.compl]
    exact unitAtomMeasure_compl_range target
  have hdistance :
      ∀ᵐ z ∂c.plan,
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal (realL1Distance z.1 z.2) := by
    filter_upwards [hfst, hsnd] with z hzS hzT
    obtain ⟨i, hi⟩ := hzS
    obtain ⟨j, hj⟩ := hzT
    rw [← hi, ← hj]
    exact ENNReal.one_le_ofReal.2 (hsep i j)
  calc
    (Fintype.card I : ℝ≥0∞) =
        ∫⁻ _ : RealGrade n × RealGrade n, (1 : ℝ≥0∞) ∂c.plan := by
          rw [lintegral_const, one_mul, c.totalMass_unitAtoms]
    _ ≤ c.cost := lintegral_mono_ae hdistance

theorem matchingMeasureCoupling_cost {n : ℕ} {I : Type*}
    [Fintype I] (source target : I → RealGrade n)
    (hmatch : ∀ i, realL1Distance (source i) (target i) = 1) :
    (matchingMeasureCoupling source target).cost =
      Fintype.card I := by
  classical
  simp [L1MeasureCoupling.cost, matchingMeasureCoupling,
    lintegral_finsetSum_measure, hmatch]

/-- The standard measure-coupling `KR₁` infimum from the paper, specialized
only in its ground space to `ℝⁿ` with `ℓ¹` cost. -/
noncomputable def measureKR1 {n : ℕ}
    (mu nu : Measure (RealGrade n)) : ℝ≥0∞ :=
  sInf (Set.range fun c : L1MeasureCoupling mu nu ↦ c.cost)

/-- Exact measure-coupling transport for separated unit atoms with a
unit-cost matching.  This proves both directions over all product measures,
not merely over a preselected matrix representation. -/
theorem measureKR1_eq_card_of_separated_unit_matching {n : ℕ}
    {I : Type*} [Fintype I] (source target : I → RealGrade n)
    (hsep : ∀ i j, 1 ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = 1) :
    measureKR1 (unitAtomMeasure source) (unitAtomMeasure target) =
      Fintype.card I := by
  let c₀ := matchingMeasureCoupling source target
  apply le_antisymm
  · calc
      measureKR1 (unitAtomMeasure source) (unitAtomMeasure target) ≤
          c₀.cost := sInf_le ⟨c₀, rfl⟩
      _ = Fintype.card I :=
        matchingMeasureCoupling_cost source target hmatch
  · apply le_sInf
    rintro r ⟨c, rfl⟩
    exact c.card_le_cost_of_separated hsep

/-- Arbitrary-scale version of the measure-theoretic lower certificate. -/
theorem L1MeasureCoupling.ofReal_mul_card_le_cost_of_separated
    {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n}
    (d : ℝ)
    (c : L1MeasureCoupling (unitAtomMeasure source) (unitAtomMeasure target))
    (hsep : ∀ i j, d ≤ realL1Distance (source i) (target j)) :
    ENNReal.ofReal d * Fintype.card I ≤ c.cost := by
  let S : Set (RealGrade n) := Set.range source
  let T : Set (RealGrade n) := Set.range target
  have hS : MeasurableSet S := Set.toFinite S |>.measurableSet
  have hT : MeasurableSet T := Set.toFinite T |>.measurableSet
  have hfst : ∀ᵐ z ∂c.plan, z.1 ∈ S := by
    rw [ae_iff]
    change c.plan (Prod.fst ⁻¹' Sᶜ) = 0
    rw [c.fst_marginal Sᶜ hS.compl]
    exact unitAtomMeasure_compl_range source
  have hsnd : ∀ᵐ z ∂c.plan, z.2 ∈ T := by
    rw [ae_iff]
    change c.plan (Prod.snd ⁻¹' Tᶜ) = 0
    rw [c.snd_marginal Tᶜ hT.compl]
    exact unitAtomMeasure_compl_range target
  have hdistance :
      ∀ᵐ z ∂c.plan,
        ENNReal.ofReal d ≤ ENNReal.ofReal (realL1Distance z.1 z.2) := by
    filter_upwards [hfst, hsnd] with z hzS hzT
    obtain ⟨i, hi⟩ := hzS
    obtain ⟨j, hj⟩ := hzT
    rw [← hi, ← hj]
    exact ENNReal.ofReal_le_ofReal (hsep i j)
  calc
    ENNReal.ofReal d * Fintype.card I =
        ∫⁻ _ : RealGrade n × RealGrade n, ENNReal.ofReal d ∂c.plan := by
          rw [lintegral_const, c.totalMass_unitAtoms]
    _ ≤ c.cost := lintegral_mono_ae hdistance

theorem matchingMeasureCoupling_cost_eq_mul_card
    {n : ℕ} {I : Type*} [Fintype I]
    (d : ℝ) (source target : I → RealGrade n)
    (hmatch : ∀ i, realL1Distance (source i) (target i) = d) :
    (matchingMeasureCoupling source target).cost =
      ENNReal.ofReal d * Fintype.card I := by
  classical
  simp [L1MeasureCoupling.cost, matchingMeasureCoupling,
    lintegral_finsetSum_measure, hmatch, mul_comm]

/-- Exact measure-coupling transport at an arbitrary common separation and
matching scale. -/
theorem measureKR1_eq_ofReal_mul_card_of_separated_matching
    {n : ℕ} {I : Type*} [Fintype I]
    (d : ℝ) (source target : I → RealGrade n)
    (hsep : ∀ i j, d ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = d) :
    measureKR1 (unitAtomMeasure source) (unitAtomMeasure target) =
      ENNReal.ofReal d * Fintype.card I := by
  let c₀ := matchingMeasureCoupling source target
  apply le_antisymm
  · calc
      measureKR1 (unitAtomMeasure source) (unitAtomMeasure target) ≤
          c₀.cost := sInf_le ⟨c₀, rfl⟩
      _ = ENNReal.ofReal d * Fintype.card I :=
        matchingMeasureCoupling_cost_eq_mul_card d source target hmatch
  · apply le_sInf
    rintro r ⟨c, rfl⟩
    exact c.ofReal_mul_card_le_cost_of_separated d hsep

theorem counterexample_isUnitAtomicJordanRepresentation (m : ℕ) (hm : 1 ≤ m) :
    IsUnitAtomicJordanRepresentation (hilbertDifferenceMeasure m)
      (counterexampleSourcePoint m) (counterexampleTargetPoint m) :=
  ⟨counterexampleSourcePoint_injective m,
    counterexampleTargetPoint_injective m,
    counterexampleSourcePoint_ne_targetPoint hm,
    hilbertDifferenceMeasure_eq_indexed_jordan m⟩

/-- Consequently, the exact coupling computation is the standard `KR₁`
norm of the Hilbert signed measure's Jordan parts. -/
theorem hilbertDifferenceMeasure_KR1 (m : ℕ) (hm : 1 ≤ m) :
    IsUnitAtomicJordanRepresentation (hilbertDifferenceMeasure m)
        (counterexampleSourcePoint m) (counterexampleTargetPoint m) ∧
      unitAtomicKR1 (counterexampleSourcePoint m) (counterexampleTargetPoint m) =
        2 * m :=
  ⟨counterexample_isUnitAtomicJordanRepresentation m hm,
    counterexample_unitAtomicKR1 m hm⟩

/-- The same exact value for the paper's product-measure/marginal/integral
definition of `KR₁`, applied literally to the Mathlib Jordan parts. -/
theorem hilbertDifferenceMeasure_measureKR1 (m : ℕ) (hm : 1 ≤ m) :
    measureKR1
        (hilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.posPart
        (hilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.negPart =
      (2 * m : ℕ) := by
  let hJordan := counterexample_isUnitAtomicJordanRepresentation m hm
  rw [hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    measureKR1_eq_card_of_separated_unit_matching
      (counterexampleSourcePoint m) (counterexampleTargetPoint m)
      (one_le_counterexample_source_target_distance hm)
      (counterexample_corresponding_distance m),
    card_counterexampleAtomIndex hm]

/-! ## Chain-level bridge for ordinary graph `H₀` -/

/-- Component augmentation on zero-chains: coefficients at vertices in the
same connected component are added. -/
noncomputable def graphComponentSum (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) :
    (V →₀ K) →ₗ[K] (G.ConnectedComponent →₀ K) :=
  Finsupp.lmapDomain K K G.connectedComponentMk

theorem graphComponentSum_surjective (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) :
    Function.Surjective (graphComponentSum K G) := by
  change Function.Surjective (Finsupp.mapDomain G.connectedComponentMk)
  exact Finsupp.mapDomain_surjective Quot.mk_surjective

/-- Degree-zero graph homology as zero-chains modulo componentwise
zero-sum relations.  The following equivalence proves this quotient is the
usual free vector space on connected components. -/
abbrev GraphChainH0 (K : Type*) [Field K] {V : Type*} (G : SimpleGraph V) :=
  (V →₀ K) ⧸ LinearMap.ker (graphComponentSum K G)

noncomputable def graphChainH0EquivComponents (K : Type*) [Field K]
    {V : Type*} [Finite V] (G : SimpleGraph V) :
    GraphChainH0 K G ≃ₗ[K] GraphH0 K G :=
  ((graphComponentSum K G).quotKerEquivOfSurjective
      (graphComponentSum_surjective K G)).trans
    (Finsupp.linearEquivFunOnFinite K K G.ConnectedComponent)

/-- Every cellular edge boundary is killed by component augmentation. -/
theorem edgeBoundary_mem_graphComponentSum_ker (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) :
    Finsupp.single v (1 : K) - Finsupp.single w 1 ∈
      LinearMap.ker (graphComponentSum K G) := by
  rw [LinearMap.mem_ker, map_sub]
  simp [graphComponentSum, Finsupp.lmapDomain_apply,
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw]

/-- Span of the actual oriented cellular edge boundaries. -/
noncomputable def cellularEdgeBoundarySpan (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) : Submodule K (V →₀ K) :=
  Submodule.span K {z | ∃ v w, G.Adj v w ∧
    z = Finsupp.single v (1 : K) - Finsupp.single w 1}

theorem walkBoundary_mem_cellularEdgeBoundarySpan (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) {v w : V} (p : G.Walk v w) :
    Finsupp.single v (1 : K) - Finsupp.single w 1 ∈
      cellularEdgeBoundarySpan K G := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have hedge : Finsupp.single u (1 : K) - Finsupp.single v 1 ∈
          cellularEdgeBoundarySpan K G :=
        Submodule.subset_span ⟨u, v, huv, rfl⟩
      have heq : Finsupp.single u (1 : K) - Finsupp.single w 1 =
          (Finsupp.single u 1 - Finsupp.single v 1) +
            (Finsupp.single v 1 - Finsupp.single w 1) := by
        abel
      rw [heq]
      exact (cellularEdgeBoundarySpan K G).add_mem hedge ih

theorem reachableBoundary_mem_cellularEdgeBoundarySpan (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) {v w : V} (hvw : G.Reachable v w) :
    Finsupp.single v (1 : K) - Finsupp.single w 1 ∈
      cellularEdgeBoundarySpan K G := by
  obtain ⟨p⟩ := hvw
  exact walkBoundary_mem_cellularEdgeBoundarySpan K G p

theorem cellularEdgeBoundarySpan_le_componentSum_ker (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) :
    cellularEdgeBoundarySpan K G ≤ LinearMap.ker (graphComponentSum K G) := by
  apply Submodule.span_le.2
  rintro z ⟨v, w, hvw, rfl⟩
  exact edgeBoundary_mem_graphComponentSum_ker K G hvw

/-- The genuine cellular chain definition `C₀ / im ∂₁`. -/
abbrev CellularGraphH0 (K : Type*) [Field K] {V : Type*} (G : SimpleGraph V) :=
  (V →₀ K) ⧸ cellularEdgeBoundarySpan K G

noncomputable def componentRepresentative {V : Type*} (G : SimpleGraph V) :
    G.ConnectedComponent → V := fun c ↦ Quot.out c

@[simp]
theorem connectedComponentMk_componentRepresentative {V : Type*}
    (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (componentRepresentative G c) = c := by
  exact Quot.out_eq c

theorem vertex_reachable_componentRepresentative {V : Type*}
    (G : SimpleGraph V) (v : V) :
    G.Reachable v (componentRepresentative G (G.connectedComponentMk v)) := by
  rw [← SimpleGraph.ConnectedComponent.eq]
  simp

noncomputable def cellularH0ToComponents (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) :
    CellularGraphH0 K G →ₗ[K] (G.ConnectedComponent →₀ K) :=
  (cellularEdgeBoundarySpan K G).liftQ (graphComponentSum K G)
    (cellularEdgeBoundarySpan_le_componentSum_ker K G)

noncomputable def componentsToCellularH0 (K : Type*) [Field K]
    {V : Type*} (G : SimpleGraph V) :
    (G.ConnectedComponent →₀ K) →ₗ[K] CellularGraphH0 K G :=
  (cellularEdgeBoundarySpan K G).mkQ.comp
    (Finsupp.lmapDomain K K (componentRepresentative G))

theorem cellularH0ToComponents_comp_componentsToCellularH0
    (K : Type*) [Field K] {V : Type*} (G : SimpleGraph V) :
    (cellularH0ToComponents K G).comp (componentsToCellularH0 K G) =
      LinearMap.id := by
  ext c
  simp [cellularH0ToComponents, componentsToCellularH0,
    graphComponentSum, Finsupp.lmapDomain_apply]

theorem componentsToCellularH0_comp_cellularH0ToComponents
    (K : Type*) [Field K] {V : Type*} (G : SimpleGraph V) :
    (componentsToCellularH0 K G).comp (cellularH0ToComponents K G) =
      LinearMap.id := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro v c
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [cellularH0ToComponents, Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [componentsToCellularH0, graphComponentSum,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    LinearMap.comp_apply]
  change (cellularEdgeBoundarySpan K G).mkQ
      (Finsupp.single (componentRepresentative G (G.connectedComponentMk v)) c) =
    (cellularEdgeBoundarySpan K G).mkQ (Finsupp.single v c)
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have hboundary := reachableBoundary_mem_cellularEdgeBoundarySpan K G
    (vertex_reachable_componentRepresentative G v)
  have hscaled : c • (Finsupp.single v (1 : K) -
      Finsupp.single (componentRepresentative G (G.connectedComponentMk v)) 1) ∈
      cellularEdgeBoundarySpan K G :=
    (cellularEdgeBoundarySpan K G).smul_mem c hboundary
  simpa [smul_sub] using (cellularEdgeBoundarySpan K G).neg_mem hscaled

/-- Actual cellular graph `H₀` is linearly equivalent to the free vector
space on connected components. -/
noncomputable def cellularGraphH0EquivComponents (K : Type*) [Field K]
    {V : Type*} [Finite V] (G : SimpleGraph V) :
    CellularGraphH0 K G ≃ₗ[K] GraphH0 K G := by
  let e : CellularGraphH0 K G ≃ₗ[K] (G.ConnectedComponent →₀ K) :=
    { toLinearMap := cellularH0ToComponents K G
      invFun := componentsToCellularH0 K G
      left_inv := fun q ↦ LinearMap.congr_fun
        (componentsToCellularH0_comp_cellularH0ToComponents K G) q
      right_inv := fun z ↦ LinearMap.congr_fun
        (cellularH0ToComponents_comp_componentsToCellularH0 K G) z }
  exact e.trans (Finsupp.linearEquivFunOnFinite K K G.ConnectedComponent)

theorem finrank_cellularGraphH0 (K : Type*) [Field K]
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Module.finrank K (CellularGraphH0 K G) = Nat.card G.ConnectedComponent := by
  rw [(cellularGraphH0EquivComponents K G).finrank_eq]
  exact finrank_graphH0 K G

/-- The actual cellular degree-zero module of a common-vertex-grade filtered
graph at a parameter `x`: it is zero before the vertices enter and
`C₀ / im ∂₁` afterwards.  The all-vertices test makes the intended sublevel
semantics explicit. -/
noncomputable def commonVertexFilteredGraphH0
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) : ModuleCat K := by
  classical
  exact if realAllVerticesActive F x then
      ModuleCat.of K (CellularGraphH0 K (realSublevelGraph F x))
    else
      ModuleCat.of K (Fin 0 → K)

/-- For a common-vertex-grade filtration, the component-count function used
throughout the finite calculation is pointwise the dimension of the genuine
cellular `H₀` module, over every coefficient field and at every parameter. -/
theorem finrank_commonVertexFilteredGraphH0
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (hcommon : CommonVertexGrade F)
    (x : RealGrade n) :
    Module.finrank K (commonVertexFilteredGraphH0 K F x) =
      realOrdinaryH0Dim F x := by
  classical
  by_cases hactive : realVerticesActive F x
  · have hall : realAllVerticesActive F x :=
      (realAllVerticesActive_iff hcommon x).2 hactive
    rw [realOrdinaryH0Dim, if_pos hactive]
    change Module.finrank K
        ↑(if realAllVerticesActive F x then
            ModuleCat.of K (CellularGraphH0 K (realSublevelGraph F x))
          else ModuleCat.of K (Fin 0 → K)) =
      Nat.card (realSublevelGraph F x).ConnectedComponent
    rw [if_pos hall]
    exact finrank_cellularGraphH0 K (realSublevelGraph F x)
  · have hall : ¬ realAllVerticesActive F x := by
      simpa [realAllVerticesActive_iff hcommon x] using hactive
    rw [realOrdinaryH0Dim, if_neg hactive]
    change Module.finrank K
        ↑(if realAllVerticesActive F x then
            ModuleCat.of K (CellularGraphH0 K (realSublevelGraph F x))
          else ModuleCat.of K (Fin 0 → K)) = 0
    rw [if_neg hall]
    simp

/-- Public all-fields, all-parameters bridge certifying that the displayed
Hilbert function is ordinary cellular `H₀`, including before the common
vertex grade enters. -/
def IsCommonVertexOrdinaryH0Model {m n : ℕ}
    (F : Simplex m → RealGrade n) : Prop :=
  CommonVertexGrade F ∧
    ∀ (K : Type*) [Field K] (x : RealGrade n),
      Module.finrank K (commonVertexFilteredGraphH0 K F x) =
        realOrdinaryH0Dim F x

theorem isCommonVertexOrdinaryH0Model_of_common {m n : ℕ}
    {F : Simplex m → RealGrade n} (hcommon : CommonVertexGrade F) :
    IsCommonVertexOrdinaryH0Model F := by
  refine ⟨hcommon, ?_⟩
  intro K _ x
  exact finrank_commonVertexFilteredGraphH0 K F hcommon x

/-- The chain quotient has component-count dimension, making the
component-count model used above a proved ordinary-`H₀` model. -/
theorem finrank_graphChainH0 (K : Type*) [Field K]
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Module.finrank K (GraphChainH0 K G) = Nat.card G.ConnectedComponent := by
  rw [(graphChainH0EquivComponents K G).finrank_eq]
  exact finrank_graphH0 K G

/-! ## Zero-padding to every dimension at least three -/

def Grade.zeroPad {n k : ℕ} (a : Grade n) : Grade (n + k) :=
  Fin.addCases a (fun _ ↦ 0)

def RealGrade.zero {k : ℕ} : RealGrade k := fun _ ↦ 0

def RealGrade.zeroPad {n k : ℕ} (a : RealGrade n) : RealGrade (n + k) :=
  concatGrade a RealGrade.zero

def leftCoordinates {n k : ℕ} (x : RealGrade (n + k)) : RealGrade n :=
  fun i ↦ x (Fin.castAdd k i)

def rightCoordinates {n k : ℕ} (x : RealGrade (n + k)) : RealGrade k :=
  fun j ↦ x (Fin.natAdd n j)

theorem concat_left_right {n k : ℕ} (x : RealGrade (n + k)) :
    concatGrade (leftCoordinates x) (rightCoordinates x) = x := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [concatGrade, leftCoordinates]
  · simp [concatGrade, rightCoordinates]

def allNonnegative {k : ℕ} (y : RealGrade k) : Prop := ∀ j, 0 ≤ y j

noncomputable def restrictNatToNonnegative {k : ℕ}
    (y : RealGrade k) (a : ℕ) : ℕ := by
  classical
  exact if allNonnegative y then a else 0

noncomputable def nonnegativeIndicator {k : ℕ} (y : RealGrade k) : ℤ := by
  classical
  exact if allNonnegative y then 1 else 0

theorem Grade.leReal_zeroPad_concat_iff {n k : ℕ}
    (a : Grade n) (x : RealGrade n) (y : RealGrade k) :
    Grade.leReal a.zeroPad (concatGrade x y) ↔
      Grade.leReal a x ∧ allNonnegative y := by
  constructor
  · intro h
    exact ⟨fun i ↦ by
        simpa [Grade.zeroPad, concatGrade] using h (Fin.castAdd k i),
      fun j ↦ by
        simpa [Grade.zeroPad, concatGrade] using h (Fin.natAdd n j)⟩
  · rintro ⟨hx, hy⟩ i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [Grade.zeroPad, concatGrade] using hx j
    · simpa [Grade.zeroPad, concatGrade] using hy j

def padFiltration {m n k : ℕ} (F : Simplex m → Grade n) :
    Simplex m → Grade (n + k) := fun sigma ↦ (F sigma).zeroPad

theorem padFiltration_monotone {m n k : ℕ} {F : Simplex m → Grade n}
    (hF : MonotoneFiltration F) : MonotoneFiltration (padFiltration (k := k) F) := by
  intro e v hv i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [padFiltration, Grade.zeroPad, Grade.LE] using hF e v hv j
  · simp [padFiltration, Grade.zeroPad]

def fGradePadded (m k : ℕ) : Simplex m → Grade (3 + k) :=
  padFiltration (k := k) (fGrade m)

def gGradePadded (m k : ℕ) : Simplex m → Grade (3 + k) :=
  padFiltration (k := k) (gGrade m)

theorem fGradePadded_monotone (m k : ℕ) :
    MonotoneFiltration (fGradePadded m k) :=
  padFiltration_monotone (fGrade_monotone m)

theorem gGradePadded_monotone (m k : ℕ) :
    MonotoneFiltration (gGradePadded m k) :=
  padFiltration_monotone (gGrade_monotone m)

theorem fGradePadded_commonVertexGrade (m k : ℕ) :
    CommonVertexGrade (realifyFiltration (fGradePadded m k)) := by
  intro v
  rfl

theorem gGradePadded_commonVertexGrade (m k : ℕ) :
    CommonVertexGrade (realifyFiltration (gGradePadded m k)) := by
  intro v
  rfl

theorem fGradePadded_gGradePadded_onlyCentralEdgeDiffers (m k : ℕ) :
    OnlyCentralEdgeDiffers
      (realifyFiltration (fGradePadded m k))
      (realifyFiltration (gGradePadded m k)) := by
  intro sigma hsigma
  cases sigma with
  | vertex v => rfl
  | edge edge =>
      cases edge with
      | e => exact (hsigma rfl).elim
      | a j => rfl
      | b j => rfl

theorem l1Distance_zeroPad {n k : ℕ} (a b : Grade n) :
    l1Distance (Grade.zeroPad (k := k) a) (Grade.zeroPad b) = l1Distance a b := by
  simp [l1Distance, Grade.zeroPad, Fin.sum_univ_add]

theorem filtrationL1Distance_padFiltration {m n k : ℕ}
    (F G : Simplex m → Grade n) :
    filtrationL1Distance (padFiltration (k := k) F) (padFiltration G) =
      filtrationL1Distance F G := by
  simp [filtrationL1Distance, padFiltration, l1Distance_zeroPad]

theorem filtrationL1Distance_fGradePadded_gGradePadded (m k : ℕ) :
    filtrationL1Distance (fGradePadded m k) (gGradePadded m k) = 1 := by
  rw [fGradePadded, gGradePadded, filtrationL1Distance_padFiltration,
    filtrationL1Distance_fGrade_gGrade]

theorem edgeActive_padFiltration_concat_iff {m n k : ℕ}
    (F : Simplex m → Grade n) (x : RealGrade n) (y : RealGrade k)
    (e : Edge m) :
    edgeActive (padFiltration (k := k) F) (concatGrade x y) e ↔
      edgeActive F x e ∧ allNonnegative y := by
  exact Grade.leReal_zeroPad_concat_iff (F (.edge e)) x y

theorem verticesActive_padFiltration_concat_iff {m n k : ℕ}
    (F : Simplex m → Grade n) (x : RealGrade n) (y : RealGrade k) :
    verticesActive (padFiltration (k := k) F) (concatGrade x y) ↔
      verticesActive F x ∧ allNonnegative y := by
  exact Grade.leReal_zeroPad_concat_iff (F (.vertex .s)) x y

theorem sublevelGraph_padFiltration_concat_eq {m n k : ℕ}
    (F : Simplex m → Grade n) (x : RealGrade n) (y : RealGrade k)
    (hy : allNonnegative y) :
    sublevelGraph (padFiltration (k := k) F) (concatGrade x y) =
      sublevelGraph F x := by
  ext v w
  cases v <;> cases w <;>
    simp [sublevelGraph, edgeActive_padFiltration_concat_iff, hy]

theorem ordinaryH0Dim_padFiltration_concat {m n k : ℕ}
    (F : Simplex m → Grade n) (x : RealGrade n) (y : RealGrade k) :
    ordinaryH0Dim (padFiltration (k := k) F) (concatGrade x y) =
      restrictNatToNonnegative y (ordinaryH0Dim F x) := by
  classical
  by_cases hy : allNonnegative y
  · rw [restrictNatToNonnegative, if_pos hy]
    by_cases hv : verticesActive F x
    · have hvpad : verticesActive (padFiltration (k := k) F)
          (concatGrade x y) :=
        (verticesActive_padFiltration_concat_iff F x y).2 ⟨hv, hy⟩
      unfold ordinaryH0Dim
      rw [if_pos hvpad, if_pos hv,
        sublevelGraph_padFiltration_concat_eq F x y hy]
    · have hvpad : ¬ verticesActive (padFiltration (k := k) F)
          (concatGrade x y) := by
        rw [verticesActive_padFiltration_concat_iff]
        tauto
      simp [ordinaryH0Dim, hv, hvpad]
  · rw [restrictNatToNonnegative, if_neg hy]
    have hvpad : ¬ verticesActive (padFiltration (k := k) F)
        (concatGrade x y) := by
      rw [verticesActive_padFiltration_concat_iff]
      tauto
    simp [ordinaryH0Dim, hvpad]

noncomputable def h0HilbertDifferencePadded (m k : ℕ)
    (x : RealGrade (3 + k)) : ℤ :=
  (ordinaryH0Dim (fGradePadded m k) x : ℤ) -
    (ordinaryH0Dim (gGradePadded m k) x : ℤ)

theorem h0HilbertDifferencePadded_concat (m k : ℕ)
    (x : RealGrade 3) (y : RealGrade k) :
    h0HilbertDifferencePadded m k (concatGrade x y) =
      nonnegativeIndicator y * h0HilbertDifference m x := by
  rw [h0HilbertDifferencePadded, fGradePadded, gGradePadded,
    ordinaryH0Dim_padFiltration_concat,
    ordinaryH0Dim_padFiltration_concat]
  by_cases hy : allNonnegative y <;>
    simp [hy, h0HilbertDifference, restrictNatToNonnegative,
      nonnegativeIndicator]

/-- Tensoring with a zero-coordinate Dirac atom implements zero-padding of
finite signed measures. -/
noncomputable def hilbertDifferenceMeasurePadded (m k : ℕ) :
    AtomicSignedMeasure (3 + k) :=
  AtomicSignedMeasure.tensor (hilbertDifferenceMeasure m)
    (atom (RealGrade.zero : RealGrade k))

/-- Zero-padded Hilbert signed measure of `H₀(fₘ)` itself. -/
noncomputable def h0FMeasurePadded (m k : ℕ) :
    AtomicSignedMeasure (3 + k) :=
  AtomicSignedMeasure.tensor (h0FMeasure m)
    (atom (RealGrade.zero : RealGrade k))

/-- Zero-padded Hilbert signed measure of `H₀(gₘ)` itself. -/
noncomputable def h0GMeasurePadded (m k : ℕ) :
    AtomicSignedMeasure (3 + k) :=
  AtomicSignedMeasure.tensor (h0GMeasure m)
    (atom (RealGrade.zero : RealGrade k))

theorem lowerIndicator_zero (k : ℕ) (y : RealGrade k) :
    lowerIndicator (RealGrade.zero : RealGrade k) y =
      nonnegativeIndicator y := by
  classical
  by_cases hy : allNonnegative y
  · have hle : RealGrade.LE (RealGrade.zero : RealGrade k) y := by
      simpa [RealGrade.LE, RealGrade.zero, allNonnegative] using hy
    simp [lowerIndicator, lowerCoefficientHom, hle, hy, nonnegativeIndicator]
  · have hnle : ¬ RealGrade.LE (RealGrade.zero : RealGrade k) y := by
      simpa [RealGrade.LE, RealGrade.zero, allNonnegative] using hy
    simp [lowerIndicator, lowerCoefficientHom, hnle, hy, nonnegativeIndicator]

theorem cumulative_h0FMeasurePadded_concat (m k : ℕ)
    (x : RealGrade 3) (y : RealGrade k) :
    cumulative (h0FMeasurePadded m k) (concatGrade x y) =
      (ordinaryH0Dim (fGradePadded m k) (concatGrade x y) : ℤ) := by
  rw [h0FMeasurePadded, cumulative_tensor, cumulative_atom,
    lowerIndicator_zero, h0FMeasure_isHilbertDecomposition,
    fGradePadded, ordinaryH0Dim_padFiltration_concat]
  by_cases hy : allNonnegative y <;>
    simp [hy, nonnegativeIndicator, restrictNatToNonnegative]

theorem cumulative_h0GMeasurePadded_concat (m k : ℕ)
    (x : RealGrade 3) (y : RealGrade k) :
    cumulative (h0GMeasurePadded m k) (concatGrade x y) =
      (ordinaryH0Dim (gGradePadded m k) (concatGrade x y) : ℤ) := by
  rw [h0GMeasurePadded, cumulative_tensor, cumulative_atom,
    lowerIndicator_zero, h0GMeasure_isHilbertDecomposition,
    gGradePadded, ordinaryH0Dim_padFiltration_concat]
  by_cases hy : allNonnegative y <;>
    simp [hy, nonnegativeIndicator, restrictNatToNonnegative]

theorem h0FMeasurePadded_isHilbertDecomposition (m k : ℕ) :
    IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (fGradePadded m k) x : ℤ))
      (h0FMeasurePadded m k) := by
  intro x
  rw [← concat_left_right x]
  exact cumulative_h0FMeasurePadded_concat m k
    (leftCoordinates x) (rightCoordinates x)

theorem h0GMeasurePadded_isHilbertDecomposition (m k : ℕ) :
    IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (gGradePadded m k) x : ℤ))
      (h0GMeasurePadded m k) := by
  intro x
  rw [← concat_left_right x]
  exact cumulative_h0GMeasurePadded_concat m k
    (leftCoordinates x) (rightCoordinates x)

theorem cumulative_hilbertDifferenceMeasurePadded_concat (m k : ℕ)
    (x : RealGrade 3) (y : RealGrade k) :
    cumulative (hilbertDifferenceMeasurePadded m k) (concatGrade x y) =
      h0HilbertDifferencePadded m k (concatGrade x y) := by
  rw [hilbertDifferenceMeasurePadded, cumulative_tensor, cumulative_atom,
    cumulative_hilbertDifferenceMeasure, lowerIndicator_zero,
    h0HilbertDifferencePadded_concat]
  ring

theorem hilbertDifferenceMeasurePadded_isHilbertDecomposition (m k : ℕ) :
    IsHilbertDecomposition (h0HilbertDifferencePadded m k)
      (hilbertDifferenceMeasurePadded m k) := by
  intro x
  rw [← concat_left_right x]
  exact cumulative_hilbertDifferenceMeasurePadded_concat m k
    (leftCoordinates x) (rightCoordinates x)

def counterexampleSourcePointPadded (m k : ℕ)
    (i : CounterexampleAtomIndex m) : RealGrade (3 + k) :=
  concatGrade (counterexampleSourcePoint m i) RealGrade.zero

def counterexampleTargetPointPadded (m k : ℕ)
    (i : CounterexampleAtomIndex m) : RealGrade (3 + k) :=
  concatGrade (counterexampleTargetPoint m i) RealGrade.zero

theorem realL1Distance_zeroPad {n k : ℕ} (a b : RealGrade n) :
    realL1Distance (concatGrade a (RealGrade.zero : RealGrade k))
      (concatGrade b RealGrade.zero) = realL1Distance a b := by
  simp [realL1Distance, concatGrade, RealGrade.zero, Fin.sum_univ_add]

theorem counterexampleSourcePointPadded_injective (m k : ℕ) :
    Function.Injective (counterexampleSourcePointPadded m k) := by
  intro i j h
  apply counterexampleSourcePoint_injective m
  funext q
  have hq := congrFun h (Fin.castAdd k q)
  simpa [counterexampleSourcePointPadded, concatGrade] using hq

theorem counterexampleTargetPointPadded_injective (m k : ℕ) :
    Function.Injective (counterexampleTargetPointPadded m k) := by
  intro i j h
  apply counterexampleTargetPoint_injective m
  funext q
  have hq := congrFun h (Fin.castAdd k q)
  simpa [counterexampleTargetPointPadded, concatGrade] using hq

theorem counterexampleSourcePointPadded_ne_targetPointPadded {m : ℕ}
    (hm : 1 ≤ m) (k : ℕ) (i j : CounterexampleAtomIndex m) :
    counterexampleSourcePointPadded m k i ≠
      counterexampleTargetPointPadded m k j := by
  intro h
  apply counterexampleSourcePoint_ne_targetPoint hm i j
  funext q
  have hq := congrFun h (Fin.castAdd k q)
  simpa [counterexampleSourcePointPadded, counterexampleTargetPointPadded,
    concatGrade] using hq

theorem AtomicSignedMeasure.tensor_fintype_sum_left {n k : ℕ}
    {I : Type*} [Fintype I] (mu : I → AtomicSignedMeasure n)
    (nu : AtomicSignedMeasure k) :
    AtomicSignedMeasure.tensor (∑ i, mu i) nu =
      ∑ i, AtomicSignedMeasure.tensor (mu i) nu := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [AtomicSignedMeasure.tensor_zero_left]
  | @insert i s hi ih =>
      simp [hi, AtomicSignedMeasure.tensor_add_left, ih]

theorem hilbertDifferenceMeasurePadded_eq_indexed_jordan (m k : ℕ) :
    hilbertDifferenceMeasurePadded m k =
      (∑ i : CounterexampleAtomIndex m,
        atom (counterexampleSourcePointPadded m k i)) -
      ∑ i : CounterexampleAtomIndex m,
        atom (counterexampleTargetPointPadded m k i) := by
  rw [hilbertDifferenceMeasurePadded,
    hilbertDifferenceMeasure_eq_indexed_jordan,
    AtomicSignedMeasure.tensor_sub_left,
    AtomicSignedMeasure.tensor_fintype_sum_left,
    AtomicSignedMeasure.tensor_fintype_sum_left]
  simp [counterexampleSourcePointPadded, counterexampleTargetPointPadded,
    AtomicSignedMeasure.tensor_atom_atom]

theorem counterexamplePadded_isUnitAtomicJordanRepresentation
    (m k : ℕ) (hm : 1 ≤ m) :
    IsUnitAtomicJordanRepresentation (hilbertDifferenceMeasurePadded m k)
      (counterexampleSourcePointPadded m k)
      (counterexampleTargetPointPadded m k) :=
  ⟨counterexampleSourcePointPadded_injective m k,
    counterexampleTargetPointPadded_injective m k,
    counterexampleSourcePointPadded_ne_targetPointPadded hm k,
    hilbertDifferenceMeasurePadded_eq_indexed_jordan m k⟩

theorem one_le_counterexamplePadded_source_target_distance {m : ℕ}
    (hm : 1 ≤ m) (k : ℕ) (i j : CounterexampleAtomIndex m) :
    1 ≤ realL1Distance (counterexampleSourcePointPadded m k i)
      (counterexampleTargetPointPadded m k j) := by
  rw [counterexampleSourcePointPadded, counterexampleTargetPointPadded,
    realL1Distance_zeroPad]
  exact one_le_counterexample_source_target_distance hm i j

theorem counterexamplePadded_corresponding_distance (m k : ℕ)
    (i : CounterexampleAtomIndex m) :
    realL1Distance (counterexampleSourcePointPadded m k i)
      (counterexampleTargetPointPadded m k i) = 1 := by
  rw [counterexampleSourcePointPadded, counterexampleTargetPointPadded,
    realL1Distance_zeroPad]
  exact counterexample_corresponding_distance m i

theorem counterexamplePadded_unitAtomicKR1 (m k : ℕ) (hm : 1 ≤ m) :
    unitAtomicKR1 (counterexampleSourcePointPadded m k)
      (counterexampleTargetPointPadded m k) = 2 * m := by
  rw [unitAtomicKR1_eq_card_of_separated_unit_matching
    _ _ (one_le_counterexamplePadded_source_target_distance hm k)
    (counterexamplePadded_corresponding_distance m k),
    card_counterexampleAtomIndex hm]
  norm_num

theorem counterexamplePadded_measureKR1 (m k : ℕ) (hm : 1 ≤ m) :
    measureKR1
        (hilbertDifferenceMeasurePadded m k).toSignedMeasure.toJordanDecomposition.posPart
        (hilbertDifferenceMeasurePadded m k).toSignedMeasure.toJordanDecomposition.negPart =
      (2 * m : ℕ) := by
  let hJordan := counterexamplePadded_isUnitAtomicJordanRepresentation m k hm
  rw [hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    measureKR1_eq_card_of_separated_unit_matching
      (counterexampleSourcePointPadded m k)
      (counterexampleTargetPointPadded m k)
      (one_le_counterexamplePadded_source_target_distance hm k)
      (counterexamplePadded_corresponding_distance m k),
    card_counterexampleAtomIndex hm]

/-! ## Public theorem and consequences -/

theorem ordinaryH0Dim_eq_finrank_graphChainH0_of_active
    (K : Type*) [Field K] {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) (hv : verticesActive F x) :
    ordinaryH0Dim F x =
      Module.finrank K (GraphChainH0 K (sublevelGraph F x)) := by
  classical
  rw [ordinaryH0Dim, if_pos hv, finrank_graphChainH0]

/-- The component-count Hilbert function is the dimension of the genuine
cellular quotient `C₀ / im ∂₁`, not merely of a coordinate proxy. -/
theorem ordinaryH0Dim_eq_finrank_cellularGraphH0_of_active
    (K : Type*) [Field K] {m n : ℕ} (F : Simplex m → Grade n)
    (x : RealGrade n) (hv : verticesActive F x) :
    ordinaryH0Dim F x =
      Module.finrank K (CellularGraphH0 K (sublevelGraph F x)) := by
  classical
  rw [ordinaryH0Dim, if_pos hv, finrank_cellularGraphH0]

/-- Real-valued version of the cellular bridge used by the public theorem.
It holds over every coefficient field. -/
theorem realOrdinaryH0Dim_eq_finrank_cellularGraphH0_of_active
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n)
    (hv : realVerticesActive F x) :
    realOrdinaryH0Dim F x =
      Module.finrank K (CellularGraphH0 K (realSublevelGraph F x)) := by
  classical
  rw [realOrdinaryH0Dim, if_pos hv, finrank_cellularGraphH0]

theorem ordinaryH0Dim_eq_zero_of_not_active
    {m n : ℕ} (F : Simplex m → Grade n) (x : RealGrade n)
    (hv : ¬ verticesActive F x) : ordinaryH0Dim F x = 0 := by
  classical
  rw [ordinaryH0Dim, if_neg hv]

theorem realOrdinaryH0Dim_eq_zero_of_not_active
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n)
    (hv : ¬ realVerticesActive F x) : realOrdinaryH0Dim F x = 0 := by
  classical
  rw [realOrdinaryH0Dim, if_neg hv]

/-- Linearity/uniqueness bridge: whenever the two ordinary-`H₀` Hilbert
measures are presented separately, their difference is exactly the atom
formula proved above. -/
theorem hilbertDifferenceMeasure_eq_sub_of_decompositions (m : ℕ)
    {muF muG : AtomicSignedMeasure 3}
    (hF : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (fGrade m) x : ℤ)) muF)
    (hG : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (gGrade m) x : ℤ)) muG) :
    muF - muG = hilbertDifferenceMeasure m := by
  apply IsHilbertDecomposition.unique
    (hμ := fun x ↦ ?_) (hν := hilbertDifferenceMeasure_isHilbertDecomposition m)
  rw [cumulative_sub, hF x, hG x]
  rfl

theorem hilbertDifferenceSignedMeasure_eq_sub_of_decompositions (m : ℕ)
    {muF muG : AtomicSignedMeasure 3}
    (hF : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (fGrade m) x : ℤ)) muF)
    (hG : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (gGrade m) x : ℤ)) muG) :
    (hilbertDifferenceMeasure m).toSignedMeasure =
      muF.toSignedMeasure - muG.toSignedMeasure := by
  rw [← AtomicSignedMeasure.toSignedMeasure_sub,
    hilbertDifferenceMeasure_eq_sub_of_decompositions m hF hG]

theorem h0FMeasure_sub_h0GMeasure (m : ℕ) :
    h0FMeasure m - h0GMeasure m = hilbertDifferenceMeasure m :=
  hilbertDifferenceMeasure_eq_sub_of_decompositions m
    (h0FMeasure_isHilbertDecomposition m)
    (h0GMeasure_isHilbertDecomposition m)

theorem hilbertDifferenceMeasurePadded_eq_sub_of_decompositions (m k : ℕ)
    {muF muG : AtomicSignedMeasure (3 + k)}
    (hF : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (fGradePadded m k) x : ℤ)) muF)
    (hG : IsHilbertDecomposition
      (fun x ↦ (ordinaryH0Dim (gGradePadded m k) x : ℤ)) muG) :
    muF - muG = hilbertDifferenceMeasurePadded m k := by
  apply IsHilbertDecomposition.unique
    (hμ := fun x ↦ ?_)
    (hν := hilbertDifferenceMeasurePadded_isHilbertDecomposition m k)
  rw [cumulative_sub, hF x, hG x]
  rfl

theorem h0FMeasurePadded_sub_h0GMeasurePadded (m k : ℕ) :
    h0FMeasurePadded m k - h0GMeasurePadded m k =
      hilbertDifferenceMeasurePadded m k :=
  hilbertDifferenceMeasurePadded_eq_sub_of_decompositions m k
    (h0FMeasurePadded_isHilbertDecomposition m k)
    (h0GMeasurePadded_isHilbertDecomposition m k)

theorem hilbertDifferenceSignedMeasurePadded_eq_sub (m k : ℕ) :
    (hilbertDifferenceMeasurePadded m k).toSignedMeasure =
      (h0FMeasurePadded m k).toSignedMeasure -
        (h0GMeasurePadded m k).toSignedMeasure := by
  rw [← AtomicSignedMeasure.toSignedMeasure_sub,
    h0FMeasurePadded_sub_h0GMeasurePadded]

/-- The exact data needed to interpret the Jordan measures as the difference
of the two ordinary-`H₀` Hilbert signed measures.  Common vertex grades make
`finrank_commonVertexFilteredGraphH0` applicable at every parameter. -/
def IsOrdinaryH0HilbertKRPair {m n : ℕ} {I : Type*} [Fintype I]
    (F G : Simplex m → RealGrade n)
    (muF muG mu : AtomicSignedMeasure n)
    (source target : I → RealGrade n) : Prop :=
  CommonVertexGrade F ∧
  CommonVertexGrade G ∧
  RealMonotoneFiltration F ∧
  RealMonotoneFiltration G ∧
  IsHilbertDecomposition (fun x ↦ (realOrdinaryH0Dim F x : ℤ)) muF ∧
  IsHilbertDecomposition (fun x ↦ (realOrdinaryH0Dim G x : ℤ)) muG ∧
  mu = muF - muG ∧
  mu.toSignedMeasure = muF.toSignedMeasure - muG.toSignedMeasure ∧
  IsUnitAtomicJordanRepresentation mu source target ∧
  mu.toSignedMeasure.toJordanDecomposition.posPart = unitAtomMeasure source ∧
  mu.toSignedMeasure.toJordanDecomposition.negPart = unitAtomMeasure target

theorem counterexamplePadded_isOrdinaryH0HilbertKRPair
    (m k : ℕ) (hm : 1 ≤ m) :
    IsOrdinaryH0HilbertKRPair
      (realifyFiltration (fGradePadded m k))
      (realifyFiltration (gGradePadded m k))
      (h0FMeasurePadded m k) (h0GMeasurePadded m k)
      (hilbertDifferenceMeasurePadded m k)
      (counterexampleSourcePointPadded m k)
      (counterexampleTargetPointPadded m k) := by
  let hJordan := counterexamplePadded_isUnitAtomicJordanRepresentation m k hm
  exact ⟨fGradePadded_commonVertexGrade m k,
    gGradePadded_commonVertexGrade m k,
    realifyFiltration_monotone (fGradePadded_monotone m k),
    realifyFiltration_monotone (gGradePadded_monotone m k),
    h0FMeasurePadded_isHilbertDecomposition m k,
    h0GMeasurePadded_isHilbertDecomposition m k,
    (h0FMeasurePadded_sub_h0GMeasurePadded m k).symm,
    hilbertDifferenceSignedMeasurePadded_eq_sub m k,
    hJordan, hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure⟩

/-- The main `H₀` counterexample theorem, with all witnesses exposed.  The maps `F,G`
are genuinely `ℝⁿ`-valued filtrations of the concrete finite graph `graph m`.
The measures `muF,muG` separately invert their ordinary cellular-`H₀` Hilbert
functions, `mu` is their difference as an actual mathlib signed measure, and
`source,target` are exactly its mathlib Jordan parts.  Thus the final transport
identity is the published `KR₁` quantity, not merely an atom-list proxy. -/
theorem theorem1_H0_counterexample_family (n m : ℕ) (hn : 3 ≤ n) (hm : 1 ≤ m) :
    ∃ (F G : Simplex m → RealGrade n)
      (muF muG mu : AtomicSignedMeasure n)
      (source target : CounterexampleAtomIndex m → RealGrade n),
      IsCommonVertexOrdinaryH0Model F ∧
      IsCommonVertexOrdinaryH0Model G ∧
      RealMonotoneFiltration F ∧
      RealMonotoneFiltration G ∧
      OnlyCentralEdgeDiffers F G ∧
      (∀ x, realSublevelGraph F x ≤ graph m) ∧
      (∀ x, realSublevelGraph G x ≤ graph m) ∧
      realFiltrationL1Distance F G = 1 ∧
      IsHilbertDecomposition
        (fun x ↦ (realOrdinaryH0Dim F x : ℤ)) muF ∧
      IsHilbertDecomposition
        (fun x ↦ (realOrdinaryH0Dim G x : ℤ)) muG ∧
      mu = muF - muG ∧
      IsHilbertDecomposition
        (fun x ↦ (realOrdinaryH0Dim F x : ℤ) -
          (realOrdinaryH0Dim G x : ℤ)) mu ∧
      mu.toSignedMeasure = muF.toSignedMeasure - muG.toSignedMeasure ∧
      (∀ x, mu.toSignedMeasure (lowerOrthant x) =
        (((realOrdinaryH0Dim F x : ℤ) -
          (realOrdinaryH0Dim G x : ℤ) : ℤ) : ℝ)) ∧
      IsUnitAtomicJordanRepresentation mu source target ∧
      mu.toSignedMeasure.toJordanDecomposition.posPart =
        unitAtomMeasure source ∧
      mu.toSignedMeasure.toJordanDecomposition.negPart =
        unitAtomMeasure target ∧
      unitAtomicKR1 source target = 2 * m ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart =
        (2 * m : ℕ) := by
  obtain ⟨k, rfl : n = 3 + k⟩ := Nat.exists_eq_add_of_le hn
  let hJordan := counterexamplePadded_isUnitAtomicJordanRepresentation m k hm
  refine ⟨realifyFiltration (fGradePadded m k),
    realifyFiltration (gGradePadded m k),
    h0FMeasurePadded m k, h0GMeasurePadded m k,
    hilbertDifferenceMeasurePadded m k,
    counterexampleSourcePointPadded m k,
    counterexampleTargetPointPadded m k,
    isCommonVertexOrdinaryH0Model_of_common
      (fGradePadded_commonVertexGrade m k),
    isCommonVertexOrdinaryH0Model_of_common
      (gGradePadded_commonVertexGrade m k),
    realifyFiltration_monotone (fGradePadded_monotone m k),
    realifyFiltration_monotone (gGradePadded_monotone m k),
    fGradePadded_gGradePadded_onlyCentralEdgeDiffers m k,
    realSublevelGraph_le_graph
      (realifyFiltration (fGradePadded m k)),
    realSublevelGraph_le_graph
      (realifyFiltration (gGradePadded m k)), ?_,
    h0FMeasurePadded_isHilbertDecomposition m k,
    h0GMeasurePadded_isHilbertDecomposition m k,
    (h0FMeasurePadded_sub_h0GMeasurePadded m k).symm,
    hilbertDifferenceMeasurePadded_isHilbertDecomposition m k,
    hilbertDifferenceSignedMeasurePadded_eq_sub m k,
    ?_, hJordan,
    hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    counterexamplePadded_unitAtomicKR1 m k hm,
    counterexamplePadded_measureKR1 m k hm⟩
  · rw [realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    norm_num
  · intro x
    rw [AtomicSignedMeasure.toSignedMeasure_apply_lowerOrthant]
    change (cumulative (hilbertDifferenceMeasurePadded m k) x : ℝ) =
      (h0HilbertDifferencePadded m k x : ℝ)
    rw [hilbertDifferenceMeasurePadded_isHilbertDecomposition m k x]

/-- The restriction of a proposed dimension-`n` Hilbert-measure Lipschitz
bound to finite graphs of the form `Sₘ`.  Any universal filtered-complex bound
from P1/P2 necessarily implies this transparent restricted statement. -/
def HilbertH0KRBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (I : Type) [Fintype I]
    (F G : Simplex m → RealGrade n)
    (muF muG mu : AtomicSignedMeasure n)
    (source target : I → RealGrade n),
    IsOrdinaryH0HilbertKRPair F G muF muG mu source target →
    measureKR1
        mu.toSignedMeasure.toJordanDecomposition.posPart
        mu.toSignedMeasure.toJordanDecomposition.negPart ≤
      ENNReal.ofReal (C * realFiltrationL1Distance F G)

theorem counterexample_isOrdinaryH0HilbertKRPair (m : ℕ) (hm : 1 ≤ m) :
    IsOrdinaryH0HilbertKRPair
      (realifyFiltration (fGrade m)) (realifyFiltration (gGrade m))
      (h0FMeasure m) (h0GMeasure m) (hilbertDifferenceMeasure m)
      (counterexampleSourcePoint m) (counterexampleTargetPoint m) := by
  let hJordan := counterexample_isUnitAtomicJordanRepresentation m hm
  exact ⟨(by intro v; rfl),
    (by intro v; rfl),
    realifyFiltration_monotone (fGrade_monotone m),
    realifyFiltration_monotone (gGrade_monotone m),
    h0FMeasure_isHilbertDecomposition m,
    h0GMeasure_isHilbertDecomposition m,
    (h0FMeasure_sub_h0GMeasure m).symm,
    hilbertDifferenceSignedMeasure_eq_sub_of_decompositions m
      (h0FMeasure_isHilbertDecomposition m)
      (h0GMeasure_isHilbertDecomposition m),
    hJordan, hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure⟩

/-- Explicit real-valued witnesses whose ratio already exceeds the proposed
constant `n`. -/
theorem exists_counterexample_to_constant_n_P1 (n : ℕ) (hn : 3 ≤ n) :
    ∃ (m : ℕ) (F G : Simplex m → RealGrade n)
      (muF muG mu : AtomicSignedMeasure n)
      (source target : CounterexampleAtomIndex m → RealGrade n),
      1 ≤ m ∧
      IsOrdinaryH0HilbertKRPair F G muF muG mu source target ∧
      realFiltrationL1Distance F G = 1 ∧
      unitAtomicKR1 source target = 2 * m ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart = (2 * m : ℕ) ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart >
        ENNReal.ofReal (n * realFiltrationL1Distance F G) := by
  obtain ⟨k, rfl : n = 3 + k⟩ := Nat.exists_eq_add_of_le hn
  let m := 3 + k + 1
  have hm : 1 ≤ m := by simp [m]
  refine ⟨m, realifyFiltration (fGradePadded m k),
    realifyFiltration (gGradePadded m k),
    h0FMeasurePadded m k, h0GMeasurePadded m k,
    hilbertDifferenceMeasurePadded m k,
    counterexampleSourcePointPadded m k,
    counterexampleTargetPointPadded m k, hm,
    counterexamplePadded_isOrdinaryH0HilbertKRPair m k hm, ?_,
    counterexamplePadded_unitAtomicKR1 m k hm,
    counterexamplePadded_measureKR1 m k hm, ?_⟩
  · rw [realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    norm_num
  · rw [counterexamplePadded_measureKR1 m k hm,
      realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    have hreal : ((3 + k : ℕ) : ℝ) < ((2 * m : ℕ) : ℝ) := by
      norm_num [m]
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
    have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by positivity
    simpa using (ENNReal.ofReal_lt_ofReal_iff hpos).2 hreal

/-- Corollary 1: the proposed constant-`n` P1 inequality is false in every
fixed dimension `n ≥ 3`. -/
theorem proposed_constant_n_P1_inequality_false (n : ℕ) (hn : 3 ≤ n) :
    ¬ HilbertH0KRBound n n := by
  obtain ⟨m, F, G, muF, muG, mu, source, target,
      _, hpair, _, _, _, hgt⟩ :=
    exists_counterexample_to_constant_n_P1 n hn
  intro hbound
  exact (not_lt_of_ge
    (hbound m (CounterexampleAtomIndex m) F G muF muG mu
      source target hpair)) hgt

/-- Quantitative unboundedness, with real-valued filtered-graph and actual
Hilbert/Jordan witnesses retained in the conclusion. -/
theorem counterexample_family_unbounded (n : ℕ) (hn : 3 ≤ n) (C : ℝ) :
    ∃ (m : ℕ) (F G : Simplex m → RealGrade n)
      (muF muG mu : AtomicSignedMeasure n)
      (source target : CounterexampleAtomIndex m → RealGrade n),
      1 ≤ m ∧
      IsOrdinaryH0HilbertKRPair F G muF muG mu source target ∧
      realFiltrationL1Distance F G = 1 ∧
      unitAtomicKR1 source target = 2 * m ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart = (2 * m : ℕ) ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart >
        ENNReal.ofReal (C * realFiltrationL1Distance F G) := by
  obtain ⟨k, rfl : n = 3 + k⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨m, hmgt⟩ := exists_nat_gt (max C 0)
  have hmreal : (0 : ℝ) < m := lt_of_le_of_lt (le_max_right C 0) hmgt
  have hmpos : 0 < m := by exact_mod_cast hmreal
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos)
  refine ⟨m, realifyFiltration (fGradePadded m k),
    realifyFiltration (gGradePadded m k),
    h0FMeasurePadded m k, h0GMeasurePadded m k,
    hilbertDifferenceMeasurePadded m k,
    counterexampleSourcePointPadded m k,
    counterexampleTargetPointPadded m k, hm,
    counterexamplePadded_isOrdinaryH0HilbertKRPair m k hm, ?_,
    counterexamplePadded_unitAtomicKR1 m k hm,
    counterexamplePadded_measureKR1 m k hm, ?_⟩
  · rw [realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    norm_num
  · rw [counterexamplePadded_measureKR1 m k hm,
      realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    have hreal : C < ((2 * m : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      nlinarith [le_max_left C 0]
    have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by positivity
    simpa using (ENNReal.ofReal_lt_ofReal_iff hpos).2 hreal

/-- Corollary 2: no finite constant depending only on the fixed dimension can
bound the Hilbert signed-measure `KR₁` distance by filtration displacement. -/
theorem no_finite_dimension_only_P2_constant (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ C : ℝ, HilbertH0KRBound n C := by
  rintro ⟨C, hbound⟩
  obtain ⟨m, F, G, muF, muG, mu, source, target,
      _, hpair, _, _, _, hgt⟩ :=
    counterexample_family_unbounded n hn C
  exact (not_lt_of_ge
    (hbound m (CounterexampleAtomIndex m) F G muF muG mu
      source target hpair)) hgt

/-- Corollary 3: `m=2` in dimension three is the explicit four-vertex graph
with exact Hilbert `KR₁` cost `4`, so `4 > 3·1`. -/
theorem n3_m2_explicit_counterexample :
    Fintype.card (Vertex 2) = 4 ∧
    Fintype.card (Edge 2) = 5 ∧
    IsOrdinaryH0HilbertKRPair
      (realifyFiltration (fGrade 2)) (realifyFiltration (gGrade 2))
      (h0FMeasure 2) (h0GMeasure 2) (hilbertDifferenceMeasure 2)
      (counterexampleSourcePoint 2) (counterexampleTargetPoint 2) ∧
    realFiltrationL1Distance (realifyFiltration (fGrade 2))
      (realifyFiltration (gGrade 2)) = 1 ∧
    unitAtomicKR1 (counterexampleSourcePoint 2) (counterexampleTargetPoint 2) = 4 ∧
    measureKR1
        (hilbertDifferenceMeasure 2).toSignedMeasure.toJordanDecomposition.posPart
        (hilbertDifferenceMeasure 2).toSignedMeasure.toJordanDecomposition.negPart = 4 ∧
    (4 : ℝ≥0∞) > ENNReal.ofReal (3 * realFiltrationL1Distance
      (realifyFiltration (fGrade 2)) (realifyFiltration (gGrade 2))) := by
  refine ⟨by decide, by decide,
    counterexample_isOrdinaryH0HilbertKRPair 2 (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [realFiltrationL1Distance_realify,
      filtrationL1Distance_fGrade_gGrade]
    norm_num
  · norm_num [counterexample_unitAtomicKR1 2 (by norm_num)]
  · norm_num [hilbertDifferenceMeasure_measureKR1 2 (by norm_num)]
  · rw [realFiltrationL1Distance_realify,
      filtrationL1Distance_fGrade_gGrade]
    norm_num

/-! ## Rescaling inside the unit cube -/

/-- Scalar dilation of a point in parameter space. -/
def scaleRealGrade {n : ℕ} (c : ℝ) (x : RealGrade n) : RealGrade n :=
  fun i ↦ c * x i

/-- The inverse coordinate change used to compare sublevel sets after a
positive dilation. -/
noncomputable def unscaleRealGrade {n : ℕ} (c : ℝ)
    (x : RealGrade n) : RealGrade n :=
  fun i ↦ x i / c

/-- Scalar dilation of every simplex grade in a filtration. -/
def scaleRealFiltration {m n : ℕ} (c : ℝ)
    (F : Simplex m → RealGrade n) : Simplex m → RealGrade n :=
  fun sigma ↦ scaleRealGrade c (F sigma)

theorem scaleRealGrade_le_iff {n : ℕ} {c : ℝ} (hc : 0 < c)
    (a x : RealGrade n) :
    RealGrade.LE (scaleRealGrade c a) x ↔
      RealGrade.LE a (unscaleRealGrade c x) := by
  constructor <;> intro h i
  · apply (le_div_iff₀ hc).2
    simpa [scaleRealGrade, mul_comm] using h i
  · have hi := (le_div_iff₀ hc).1 (h i)
    simpa [scaleRealGrade, mul_comm] using hi

theorem scaleRealFiltration_monotone {m n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {F : Simplex m → RealGrade n} (hF : RealMonotoneFiltration F) :
    RealMonotoneFiltration (scaleRealFiltration c F) := by
  intro e v hv i
  exact mul_le_mul_of_nonneg_left (hF e v hv i) hc

theorem realL1Distance_scaleRealGrade {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x y : RealGrade n) :
    realL1Distance (scaleRealGrade c x) (scaleRealGrade c y) =
      c * realL1Distance x y := by
  simp [realL1Distance, scaleRealGrade, ← mul_sub, abs_mul, abs_of_nonneg hc,
    Finset.mul_sum]

theorem realFiltrationL1Distance_scaleRealFiltration {m n : ℕ}
    {c : ℝ} (hc : 0 ≤ c) (F G : Simplex m → RealGrade n) :
    realFiltrationL1Distance (scaleRealFiltration c F)
      (scaleRealFiltration c G) =
      c * realFiltrationL1Distance F G := by
  simp [realFiltrationL1Distance, scaleRealFiltration,
    realL1Distance_scaleRealGrade hc, Finset.mul_sum]

theorem realVerticesActive_scaleRealFiltration {m n : ℕ} {c : ℝ}
    (hc : 0 < c) (F : Simplex m → RealGrade n) (x : RealGrade n) :
    realVerticesActive (scaleRealFiltration c F) x =
      realVerticesActive F (unscaleRealGrade c x) := by
  exact propext (scaleRealGrade_le_iff hc _ _)

theorem realSublevelGraph_scaleRealFiltration {m n : ℕ} {c : ℝ}
    (hc : 0 < c) (F : Simplex m → RealGrade n) (x : RealGrade n) :
    realSublevelGraph (scaleRealFiltration c F) x =
      realSublevelGraph F (unscaleRealGrade c x) := by
  ext v w
  cases v <;> cases w <;>
    simp [realSublevelGraph, realEdgeActive, scaleRealFiltration,
      scaleRealGrade_le_iff hc]

theorem realOrdinaryH0Dim_scaleRealFiltration {m n : ℕ} {c : ℝ}
    (hc : 0 < c) (F : Simplex m → RealGrade n) (x : RealGrade n) :
    realOrdinaryH0Dim (scaleRealFiltration c F) x =
      realOrdinaryH0Dim F (unscaleRealGrade c x) := by
  classical
  simp only [realOrdinaryH0Dim,
    realVerticesActive_scaleRealFiltration hc,
    realSublevelGraph_scaleRealFiltration hc]

/-- Push every atom of a finite signed point measure through scalar
dilation. -/
noncomputable def AtomicSignedMeasure.scale {n : ℕ} (c : ℝ)
    (mu : AtomicSignedMeasure n) : AtomicSignedMeasure n :=
  Finsupp.mapDomain (scaleRealGrade c) mu

theorem scaleRealGrade_injective {n : ℕ} {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (scaleRealGrade (n := n) c) := by
  intro x y h
  funext i
  exact (mul_left_cancel₀ hc (congrFun h i))

theorem lowerCoefficientHom_scale {n : ℕ} {c : ℝ} (hc : 0 < c)
    (a x : RealGrade n) :
    lowerCoefficientHom (scaleRealGrade c a) x =
      lowerCoefficientHom a (unscaleRealGrade c x) := by
  unfold lowerCoefficientHom
  rw [propext (scaleRealGrade_le_iff hc a x)]

theorem cumulative_scale {n : ℕ} {c : ℝ} (hc : 0 < c)
    (mu : AtomicSignedMeasure n) (x : RealGrade n) :
    cumulative (mu.scale c) x =
      cumulative mu (unscaleRealGrade c x) := by
  classical
  simp [AtomicSignedMeasure.scale, cumulative,
    lowerCoefficientHom_scale hc]

theorem AtomicSignedMeasure.scale_atom {n : ℕ} (c : ℝ)
    (a : RealGrade n) :
    (atom a).scale c = atom (scaleRealGrade c a) := by
  classical
  simp [AtomicSignedMeasure.scale, atom]

theorem AtomicSignedMeasure.scale_add {n : ℕ} (c : ℝ)
    (mu nu : AtomicSignedMeasure n) :
    (mu + nu).scale c = mu.scale c + nu.scale c := by
  classical
  exact Finsupp.mapDomain_add

theorem AtomicSignedMeasure.scale_neg {n : ℕ} (c : ℝ)
    (mu : AtomicSignedMeasure n) :
    (-mu).scale c = -(mu.scale c) := by
  classical
  have h := Finsupp.mapDomain_sub
    (v₁ := (0 : AtomicSignedMeasure n)) (v₂ := mu)
    (f := scaleRealGrade c)
  simpa [AtomicSignedMeasure.scale] using h

theorem AtomicSignedMeasure.scale_sub {n : ℕ} (c : ℝ)
    (mu nu : AtomicSignedMeasure n) :
    (mu - nu).scale c = mu.scale c - nu.scale c := by
  rw [sub_eq_add_neg, AtomicSignedMeasure.scale_add,
    AtomicSignedMeasure.scale_neg, sub_eq_add_neg]

theorem IsHilbertDecomposition.scale {m n : ℕ} {c : ℝ} (hc : 0 < c)
    {F : Simplex m → RealGrade n} {mu : AtomicSignedMeasure n}
    (hmu : IsHilbertDecomposition
      (fun x ↦ (realOrdinaryH0Dim F x : ℤ)) mu) :
    IsHilbertDecomposition
      (fun x ↦ (realOrdinaryH0Dim (scaleRealFiltration c F) x : ℤ))
      (mu.scale c) := by
  intro x
  rw [cumulative_scale hc, hmu]
  simp only
  congr 1
  exact realOrdinaryH0Dim_scaleRealFiltration hc F x |>.symm

/-- The transport lower certificate with an arbitrary common separation
scale. -/
theorem UnitCoupling.mul_card_le_cost {n : ℕ} {I : Type*} [Fintype I]
    {source target : I → RealGrade n} (d : ℝ)
    (coupling : UnitCoupling source target)
    (hdistance : ∀ i j, d ≤ realL1Distance (source i) (target j)) :
    d * Fintype.card I ≤ coupling.cost := by
  calc
    d * Fintype.card I = ∑ i : I, d := by simp [mul_comm]
    _ = ∑ i : I, ∑ j : I, coupling.mass i j * d := by
      congr 1
      funext i
      rw [← Finset.sum_mul, coupling.row_sum]
      simp
    _ ≤ ∑ i : I, ∑ j : I,
        coupling.mass i j * realL1Distance (source i) (target j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hdistance i j)
        (coupling.nonnegative i j)
    _ = coupling.cost := rfl

theorem unitAtomicKR1_eq_mul_card_of_separated_matching {n : ℕ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : ℝ) (hd : 0 ≤ d) (source target : I → RealGrade n)
    (hsep : ∀ i j, d ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = d) :
    unitAtomicKR1 source target = d * Fintype.card I := by
  let c₀ := identityUnitCoupling source target
  have hcost : c₀.cost = d * Fintype.card I := by
    rw [identityUnitCoupling_cost]
    simp [hmatch, mul_comm]
  have hbounded : BddBelow {r | ∃ c : UnitCoupling source target, c.cost = r} := by
    refine ⟨0, ?_⟩
    intro r hr
    obtain ⟨c, rfl⟩ := hr
    exact c.cost_nonnegative
  apply le_antisymm
  · exact csInf_le hbounded ⟨c₀, hcost⟩
  · apply le_csInf
    · exact ⟨c₀.cost, c₀, rfl⟩
    · intro r hr
      obtain ⟨c, rfl⟩ := hr
      exact c.mul_card_le_cost d hsep

theorem unitAtomicKR1_scaled_of_separated_unit_matching {n : ℕ}
    {I : Type*} [Fintype I] [DecidableEq I]
    {c : ℝ} (hc : 0 ≤ c) (source target : I → RealGrade n)
    (hsep : ∀ i j, 1 ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = 1) :
    unitAtomicKR1 (fun i ↦ scaleRealGrade c (source i))
      (fun i ↦ scaleRealGrade c (target i)) =
      c * Fintype.card I := by
  apply unitAtomicKR1_eq_mul_card_of_separated_matching c hc
  · intro i j
    rw [realL1Distance_scaleRealGrade hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsep i j) hc
  · intro i
    rw [realL1Distance_scaleRealGrade hc, hmatch i, mul_one]

theorem measureKR1_scaled_of_separated_unit_matching {n : ℕ}
    {I : Type*} [Fintype I]
    {c : ℝ} (hc : 0 ≤ c) (source target : I → RealGrade n)
    (hsep : ∀ i j, 1 ≤ realL1Distance (source i) (target j))
    (hmatch : ∀ i, realL1Distance (source i) (target i) = 1) :
    measureKR1
        (unitAtomMeasure fun i ↦ scaleRealGrade c (source i))
        (unitAtomMeasure fun i ↦ scaleRealGrade c (target i)) =
      ENNReal.ofReal c * Fintype.card I := by
  apply measureKR1_eq_ofReal_mul_card_of_separated_matching c
  · intro i j
    rw [realL1Distance_scaleRealGrade hc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hsep i j) hc
  · intro i
    rw [realL1Distance_scaleRealGrade hc, hmatch i, mul_one]

theorem IsUnitAtomicJordanRepresentation.scale {n : ℕ}
    {I : Type*} [Fintype I] {mu : AtomicSignedMeasure n}
    {source target : I → RealGrade n} {c : ℝ} (hc : c ≠ 0)
    (h : IsUnitAtomicJordanRepresentation mu source target) :
    IsUnitAtomicJordanRepresentation (mu.scale c)
      (fun i ↦ scaleRealGrade c (source i))
      (fun i ↦ scaleRealGrade c (target i)) := by
  classical
  refine ⟨(scaleRealGrade_injective hc).comp h.1,
    (scaleRealGrade_injective hc).comp h.2.1, ?_, ?_⟩
  · intro i j hij
    exact h.2.2.1 i j ((scaleRealGrade_injective hc) hij)
  · rw [h.2.2.2, AtomicSignedMeasure.scale_sub]
    simp [AtomicSignedMeasure.scale, atom,
      Finsupp.mapDomain_finsetSum]

/-- Positive scalar dilation preserves the full ordinary-`H₀`
Hilbert/Jordan bridge, not merely the displayed atom lists. -/
theorem IsOrdinaryH0HilbertKRPair.scale {m n : ℕ}
    {I : Type*} [Fintype I]
    {F G : Simplex m → RealGrade n}
    {muF muG mu : AtomicSignedMeasure n}
    {source target : I → RealGrade n}
    {c : ℝ} (hc : 0 < c)
    (h : IsOrdinaryH0HilbertKRPair
      F G muF muG mu source target) :
    IsOrdinaryH0HilbertKRPair
      (scaleRealFiltration c F) (scaleRealFiltration c G)
      (muF.scale c) (muG.scale c) (mu.scale c)
      (fun i ↦ scaleRealGrade c (source i))
      (fun i ↦ scaleRealGrade c (target i)) := by
  rcases h with
    ⟨hcommonF, hcommonG, hF, hG, hmuF, hmuG,
      hsub, _, hJordan, _, _⟩
  have hc0 : 0 ≤ c := hc.le
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcommonFScaled :
      CommonVertexGrade (scaleRealFiltration c F) := by
    intro v
    simp [scaleRealFiltration, scaleRealGrade, hcommonF v]
  have hcommonGScaled :
      CommonVertexGrade (scaleRealFiltration c G) := by
    intro v
    simp [scaleRealFiltration, scaleRealGrade, hcommonG v]
  have hsubScaled : mu.scale c = muF.scale c - muG.scale c := by
    rw [hsub, AtomicSignedMeasure.scale_sub]
  let hJordanScaled := hJordan.scale hcne
  exact ⟨hcommonFScaled, hcommonGScaled,
    scaleRealFiltration_monotone hc0 hF,
    scaleRealFiltration_monotone hc0 hG,
    hmuF.scale hc, hmuG.scale hc, hsubScaled,
    by rw [hsubScaled, AtomicSignedMeasure.toSignedMeasure_sub],
    hJordanScaled, hJordanScaled.posPart_eq_unitAtomMeasure,
    hJordanScaled.negPart_eq_unitAtomMeasure⟩

/-- Closed unit cube in the `ℓ¹` parameter space. -/
def InUnitCube {n : ℕ} (x : RealGrade n) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 1

/-- The normalization factor used for the `m`-th counterexample. -/
noncomputable def unitScale (m : ℕ) : ℝ := ((m : ℝ)⁻¹)

theorem fGrade_coordinate_bounds {m : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) (i : Fin 3) :
    0 ≤ fGrade m sigma i ∧ fGrade m sigma i ≤ (m : ℤ) := by
  cases sigma with
  | vertex v =>
      fin_cases i <;> simp [fGrade]
  | edge e =>
      cases e with
      | e =>
          fin_cases i <;> simp [fGrade] <;> omega
      | a j =>
          fin_cases i <;> simp [fGrade] <;> omega
      | b j =>
          fin_cases i <;> simp [fGrade] <;> omega

theorem gGrade_coordinate_bounds {m : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) (i : Fin 3) :
    0 ≤ gGrade m sigma i ∧ gGrade m sigma i ≤ (m : ℤ) := by
  cases sigma with
  | vertex v =>
      fin_cases i <;> simp [gGrade]
  | edge e =>
      cases e with
      | e =>
          fin_cases i <;> simp [gGrade] <;> omega
      | a j =>
          fin_cases i <;> simp [gGrade] <;> omega
      | b j =>
          fin_cases i <;> simp [gGrade] <;> omega

theorem fGradePadded_coordinate_bounds {m k : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) (i : Fin (3 + k)) :
    0 ≤ fGradePadded m k sigma i ∧
      fGradePadded m k sigma i ≤ (m : ℤ) := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [fGradePadded, padFiltration, Grade.zeroPad] using
      fGrade_coordinate_bounds hm sigma j
  · simp [fGradePadded, padFiltration, Grade.zeroPad]

theorem gGradePadded_coordinate_bounds {m k : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) (i : Fin (3 + k)) :
    0 ≤ gGradePadded m k sigma i ∧
      gGradePadded m k sigma i ≤ (m : ℤ) := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [gGradePadded, padFiltration, Grade.zeroPad] using
      gGrade_coordinate_bounds hm sigma j
  · simp [gGradePadded, padFiltration, Grade.zeroPad]

theorem scale_to_unit_cube_of_coordinate_bounds {n m : ℕ}
    (hm : 1 ≤ m) (a : Grade n)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ (m : ℤ)) :
    InUnitCube (scaleRealGrade (unitScale m) a.toReal) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  intro i
  have ha0 : (0 : ℝ) ≤ a i := by exact_mod_cast (ha i).1
  have ham : (a i : ℝ) ≤ m := by exact_mod_cast (ha i).2
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hmreal.le) ha0
  · calc
      unitScale m * (a i : ℝ) ≤ unitScale m * (m : ℝ) :=
        mul_le_mul_of_nonneg_left ham (inv_nonneg.mpr hmreal.le)
      _ = 1 := by simp [unitScale, ne_of_gt hmreal]

theorem scaled_fGradePadded_in_unit_cube {m k : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) :
    InUnitCube
      (scaleRealFiltration (unitScale m)
        (realifyFiltration (fGradePadded m k)) sigma) := by
  apply scale_to_unit_cube_of_coordinate_bounds (hm.trans' (by omega))
  exact fGradePadded_coordinate_bounds hm sigma

theorem scaled_gGradePadded_in_unit_cube {m k : ℕ} (hm : 2 ≤ m)
    (sigma : Simplex m) :
    InUnitCube
      (scaleRealFiltration (unitScale m)
        (realifyFiltration (gGradePadded m k)) sigma) := by
  apply scale_to_unit_cube_of_coordinate_bounds (hm.trans' (by omega))
  exact gGradePadded_coordinate_bounds hm sigma

theorem unitScale_pos {m : ℕ} (hm : 1 ≤ m) : 0 < unitScale m := by
  exact inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hm))

theorem scaled_counterexamplePadded_unitAtomicKR1
    (m k : ℕ) (hm : 1 ≤ m) :
    unitAtomicKR1
      (fun i ↦ scaleRealGrade (unitScale m)
        (counterexampleSourcePointPadded m k i))
      (fun i ↦ scaleRealGrade (unitScale m)
        (counterexampleTargetPointPadded m k i)) = 2 := by
  rw [unitAtomicKR1_scaled_of_separated_unit_matching
    (unitScale_pos hm).le
    (counterexampleSourcePointPadded m k)
    (counterexampleTargetPointPadded m k)
    (one_le_counterexamplePadded_source_target_distance hm k)
    (counterexamplePadded_corresponding_distance m k),
    card_counterexampleAtomIndex hm]
  have hmne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  rw [unitScale]
  calc
    (m : ℝ)⁻¹ * (↑(2 * m) : ℝ) =
        (m : ℝ)⁻¹ * (2 * (m : ℝ)) := by
          norm_num [Nat.cast_mul]
    _ =
        2 * ((m : ℝ)⁻¹ * (m : ℝ)) := by ring
    _ = 2 := by rw [inv_mul_cancel₀ hmne, mul_one]

theorem scaled_counterexamplePadded_measureKR1
    (m k : ℕ) (hm : 1 ≤ m) :
    measureKR1
        ((hilbertDifferenceMeasurePadded m k).scale
          (unitScale m)).toSignedMeasure.toJordanDecomposition.posPart
        ((hilbertDifferenceMeasurePadded m k).scale
          (unitScale m)).toSignedMeasure.toJordanDecomposition.negPart =
      2 := by
  let hJordan :=
    (counterexamplePadded_isUnitAtomicJordanRepresentation m k hm).scale
      (unitScale_pos hm).ne'
  rw [hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    measureKR1_scaled_of_separated_unit_matching
      (unitScale_pos hm).le
      (counterexampleSourcePointPadded m k)
      (counterexampleTargetPointPadded m k)
      (one_le_counterexamplePadded_source_target_distance hm k)
      (counterexamplePadded_corresponding_distance m k),
    card_counterexampleAtomIndex hm]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  rw [unitScale, ENNReal.ofReal_inv_of_pos hmpos]
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [show (↑(2 * m) : ℝ≥0∞) = (m : ℝ≥0∞) * 2 by
    norm_num [Nat.cast_mul, mul_comm]]
  simpa only [ENNReal.ofReal_natCast] using
    (ENNReal.inv_mul_cancel_left (a := (m : ℝ≥0∞)) (b := 2) hm0 hmtop)

/-- Unit-cube strengthening of Theorem 1.  For `m ≥ 2`, every simplex grade
lies in `[0,1]ⁿ`, the input distance is `1/m`, and the exact Hilbert
signed-measure `KR₁` distance remains `2`. -/
theorem unit_cube_H0_counterexample_family
    (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    ∃ (F G : Simplex m → RealGrade n)
      (muF muG mu : AtomicSignedMeasure n)
      (source target : CounterexampleAtomIndex m → RealGrade n),
      (∀ sigma, InUnitCube (F sigma)) ∧
      (∀ sigma, InUnitCube (G sigma)) ∧
      IsOrdinaryH0HilbertKRPair F G muF muG mu source target ∧
      realFiltrationL1Distance F G = unitScale m ∧
      unitAtomicKR1 source target = 2 ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart = 2 := by
  obtain ⟨k, rfl : n = 3 + k⟩ := Nat.exists_eq_add_of_le hn
  have hm1 : 1 ≤ m := by omega
  let c := unitScale m
  let F₀ := realifyFiltration (fGradePadded m k)
  let G₀ := realifyFiltration (gGradePadded m k)
  let muF₀ := h0FMeasurePadded m k
  let muG₀ := h0GMeasurePadded m k
  let mu₀ := hilbertDifferenceMeasurePadded m k
  let source₀ := counterexampleSourcePointPadded m k
  let target₀ := counterexampleTargetPointPadded m k
  refine ⟨scaleRealFiltration c F₀, scaleRealFiltration c G₀,
    muF₀.scale c, muG₀.scale c, mu₀.scale c,
    (fun i ↦ scaleRealGrade c (source₀ i)),
    (fun i ↦ scaleRealGrade c (target₀ i)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scaled_fGradePadded_in_unit_cube hm
  · exact scaled_gGradePadded_in_unit_cube hm
  · exact (counterexamplePadded_isOrdinaryH0HilbertKRPair m k hm1).scale
      (unitScale_pos hm1)
  · rw [realFiltrationL1Distance_scaleRealFiltration
      (unitScale_pos hm1).le,
      realFiltrationL1Distance_realify,
      filtrationL1Distance_fGradePadded_gGradePadded]
    simp [c, F₀, G₀]
  · exact scaled_counterexamplePadded_unitAtomicKR1 m k hm1
  · exact scaled_counterexamplePadded_measureKR1 m k hm1

/-- Counterexamples persist at arbitrarily small filtration displacement,
even when all grades lie in a fixed unit cube and the output distance stays
equal to two. -/
theorem arbitrarily_close_unit_cube_counterexamples
    (n : ℕ) (hn : 3 ≤ n) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (F G : Simplex m → RealGrade n)
      (muF muG mu : AtomicSignedMeasure n)
      (source target : CounterexampleAtomIndex m → RealGrade n),
      2 ≤ m ∧
      (∀ sigma, InUnitCube (F sigma)) ∧
      (∀ sigma, InUnitCube (G sigma)) ∧
      IsOrdinaryH0HilbertKRPair F G muF muG mu source target ∧
      realFiltrationL1Distance F G < epsilon ∧
      unitAtomicKR1 source target = 2 ∧
      measureKR1
          mu.toSignedMeasure.toJordanDecomposition.posPart
          mu.toSignedMeasure.toJordanDecomposition.negPart = 2 := by
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hepsilon
  let m := q + 2
  have hm : 2 ≤ m := by simp [m]
  obtain ⟨F, G, muF, muG, mu, source, target,
      hcubeF, hcubeG, hpair, hdist, hkr, hmeasureKR⟩ :=
    unit_cube_H0_counterexample_family n m hn hm
  refine ⟨m, F, G, muF, muG, mu, source, target, hm,
    hcubeF, hcubeG, hpair, ?_, hkr, hmeasureKR⟩
  rw [hdist]
  have hden : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hstep :
      (1 : ℝ) / ((q : ℝ) + 2) < 1 / ((q : ℝ) + 1) := by
    exact one_div_lt_one_div_of_lt hden (by linarith)
  exact (by simpa [unitScale, one_div, m] using hstep.trans hq)

/-! ## Same-family cellular `H₁` and Euler cancellation -/

/-- A fixed orientation of the edges of `Sₘ`. -/
def edgeSource {m : ℕ} : Edge m → Vertex m
  | .e => .s
  | .a _ => .s
  | .b j => .u j

def edgeTarget {m : ℕ} : Edge m → Vertex m
  | .e => .t
  | .a j => .u j
  | .b _ => .t

theorem realSublevelGraph_adj_edgeSource_edgeTarget {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) (e : Edge m)
    (he : realEdgeActive F x e) :
    (realSublevelGraph F x).Adj (edgeSource e) (edgeTarget e) := by
  cases e with
  | e =>
      change (Vertex.s : Vertex m) ≠ .t ∧
        (realEdgeActive F x .e ∨ False)
      exact ⟨by simp, Or.inl he⟩
  | a j =>
      change (Vertex.s : Vertex m) ≠ .u j ∧
        (realEdgeActive F x (.a j) ∨ False)
      exact ⟨by simp, Or.inl he⟩
  | b j =>
      change (Vertex.u j : Vertex m) ≠ .t ∧
        (realEdgeActive F x (.b j) ∨ False)
      exact ⟨by simp, Or.inl he⟩

theorem realSublevelGraph_adj_iff_active_edge {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n)
    (v w : Vertex m) :
    (realSublevelGraph F x).Adj v w ↔
      ∃ e : Edge m, realEdgeActive F x e ∧
        ((v = edgeSource e ∧ w = edgeTarget e) ∨
          (v = edgeTarget e ∧ w = edgeSource e)) := by
  constructor
  · intro hvw
    cases v with
    | s =>
        cases w with
        | s => exact (hvw.ne rfl).elim
        | t =>
            have he : realEdgeActive F x (.e : Edge m) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.e, he, Or.inl ⟨rfl, rfl⟩⟩
        | u j =>
            have he : realEdgeActive F x (.a j) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.a j, he, Or.inl ⟨rfl, rfl⟩⟩
    | t =>
        cases w with
        | s =>
            have he : realEdgeActive F x (.e : Edge m) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.e, he, Or.inr ⟨rfl, rfl⟩⟩
        | t => exact (hvw.ne rfl).elim
        | u j =>
            have he : realEdgeActive F x (.b j) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.b j, he, Or.inr ⟨rfl, rfl⟩⟩
    | u i =>
        cases w with
        | s =>
            have he : realEdgeActive F x (.a i) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.a i, he, Or.inr ⟨rfl, rfl⟩⟩
        | t =>
            have he : realEdgeActive F x (.b i) := by
              simpa [realSublevelGraph] using hvw
            exact ⟨.b i, he, Or.inl ⟨rfl, rfl⟩⟩
        | u j =>
            have : False := by
              simpa [realSublevelGraph] using hvw
            exact this.elim
  · rintro ⟨e, he, horient⟩
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact realSublevelGraph_adj_edgeSource_edgeTarget F x e he
    · exact (realSublevelGraph_adj_edgeSource_edgeTarget F x e he).symm

/-- Edges present in a real sublevel graph. -/
abbrev ActiveEdge {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) := {e : Edge m // realEdgeActive F x e}

/-- Cellular boundary of one oriented graph edge. -/
noncomputable def edgeBoundaryVector (K : Type*) [Field K] {m : ℕ}
    (e : Edge m) : Vertex m →₀ K :=
  Finsupp.single (edgeSource e) 1 - Finsupp.single (edgeTarget e) 1

/-- The actual cellular boundary `∂₁ : C₁ → C₀` of a sublevel graph. -/
noncomputable def activeEdgeBoundary (K : Type*) [Field K]
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n) :
    (ActiveEdge F x →₀ K) →ₗ[K] (Vertex m →₀ K) :=
  Finsupp.lsum K fun e ↦
    LinearMap.id.smulRight (edgeBoundaryVector K e.1)

@[simp]
theorem activeEdgeBoundary_single (K : Type*) [Field K]
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n)
    (e : ActiveEdge F x) (c : K) :
    activeEdgeBoundary K F x (Finsupp.single e c) =
      c • edgeBoundaryVector K e.1 := by
  simp [activeEdgeBoundary]

theorem activeEdgeBoundary_range_eq_cellularEdgeBoundarySpan
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    LinearMap.range (activeEdgeBoundary K F x) =
      cellularEdgeBoundarySpan K (realSublevelGraph F x) := by
  classical
  apply le_antisymm
  · rintro z ⟨c, rfl⟩
    rw [activeEdgeBoundary, Finsupp.lsum_apply]
    change (∑ e ∈ c.support,
      c e • edgeBoundaryVector K e.1) ∈
        cellularEdgeBoundarySpan K (realSublevelGraph F x)
    apply Submodule.sum_mem
    intro e he
    apply (cellularEdgeBoundarySpan K
      (realSublevelGraph F x)).smul_mem
    apply Submodule.subset_span
    exact ⟨edgeSource e.1, edgeTarget e.1,
      realSublevelGraph_adj_edgeSource_edgeTarget F x e.1 e.2, rfl⟩
  · apply Submodule.span_le.2
    rintro z ⟨v, w, hvw, rfl⟩
    obtain ⟨e, he, horient⟩ :=
      (realSublevelGraph_adj_iff_active_edge F x v w).1 hvw
    let active : ActiveEdge F x := ⟨e, he⟩
    rcases horient with horient | horient
    · rcases horient with ⟨rfl, rfl⟩
      refine ⟨Finsupp.single active 1, ?_⟩
      simp [active, edgeBoundaryVector]
    · rcases horient with ⟨rfl, rfl⟩
      refine ⟨Finsupp.single active (-1), ?_⟩
      simp [active, edgeBoundaryVector, sub_eq_add_neg]

/-- Genuine cellular graph homology in degree one: the kernel of the
cellular edge boundary. -/
noncomputable abbrev CellularFilteredGraphH1 (K : Type*) [Field K]
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n) :=
  LinearMap.ker (activeEdgeBoundary K F x)

/-- The degree-zero quotient formed from the same cellular boundary. -/
noncomputable abbrev CellularFilteredGraphH0 (K : Type*) [Field K]
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n) :=
  (Vertex m →₀ K) ⧸ LinearMap.range (activeEdgeBoundary K F x)

theorem finrank_cellularFilteredGraphH0 (K : Type*) [Field K]
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n) :
    Module.finrank K (CellularFilteredGraphH0 K F x) =
      Nat.card (realSublevelGraph F x).ConnectedComponent := by
  classical
  let R := LinearMap.range (activeEdgeBoundary K F x)
  let S := cellularEdgeBoundarySpan K (realSublevelGraph F x)
  have hRS : R = S :=
    activeEdgeBoundary_range_eq_cellularEdgeBoundarySpan K F x
  have hR := R.finrank_quotient_add_finrank
  have hS := S.finrank_quotient_add_finrank
  have hH0 := finrank_cellularGraphH0 K (realSublevelGraph F x)
  change Module.finrank K ((Vertex m →₀ K) ⧸ R) =
    Nat.card (realSublevelGraph F x).ConnectedComponent
  change Module.finrank K ((Vertex m →₀ K) ⧸ S) =
    Nat.card (realSublevelGraph F x).ConnectedComponent at hH0
  have hfinrank : Module.finrank K R = Module.finrank K S := by
    rw [hRS]
  rw [Module.finrank_finsupp_self] at hR hS
  omega

/-- Number of one-cells in a real sublevel graph, counted using the concrete
edge type of `Sₘ`. -/
noncomputable def realActiveEdgeCount {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) : ℕ :=
  Nat.card (ActiveEdge F x)

/-- Euler--Poincaré at chain level for the filtered graph. -/
theorem finrank_cellularFilteredGraphH1_add_vertices
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    Module.finrank K (CellularFilteredGraphH1 K F x) +
        Fintype.card (Vertex m) =
      realActiveEdgeCount F x +
        Nat.card (realSublevelGraph F x).ConnectedComponent := by
  classical
  rw [realActiveEdgeCount, Nat.card_eq_fintype_card]
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (activeEdgeBoundary K F x)
  have hquot :=
    (LinearMap.range (activeEdgeBoundary K F x)).finrank_quotient_add_finrank
  have hH0 := finrank_cellularFilteredGraphH0 K F x
  change Module.finrank K
      ((Vertex m →₀ K) ⧸
        LinearMap.range (activeEdgeBoundary K F x)) =
    Nat.card (realSublevelGraph F x).ConnectedComponent at hH0
  change Module.finrank K (LinearMap.ker (activeEdgeBoundary K F x)) +
      Fintype.card (Vertex m) =
    Fintype.card (ActiveEdge F x) +
      Nat.card (realSublevelGraph F x).ConnectedComponent
  have hnull' :
      Module.finrank K
          (LinearMap.range (activeEdgeBoundary K F x)) +
          Module.finrank K
            (LinearMap.ker (activeEdgeBoundary K F x)) =
        Fintype.card (ActiveEdge F x) := by
    simpa only [Module.finrank_finsupp_self] using hnull
  have hquot' :
      Module.finrank K
          ((Vertex m →₀ K) ⧸
            LinearMap.range (activeEdgeBoundary K F x)) +
          Module.finrank K
            (LinearMap.range (activeEdgeBoundary K F x)) =
        Fintype.card (Vertex m) := by
    simpa only [Module.finrank_finsupp_self] using hquot
  omega

/-- Ordinary cellular `H₁` dimension.  The rational coefficient field is
used only to choose a coefficient-independent natural number; the next
theorem proves the same value over every field. -/
noncomputable def realOrdinaryH1Dim {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) : ℕ := by
  classical
  exact if realVerticesActive F x then
    Module.finrank ℚ (CellularFilteredGraphH1 ℚ F x)
  else 0

theorem finrank_cellularFilteredGraphH1_field_independent
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    Module.finrank K (CellularFilteredGraphH1 K F x) =
      Module.finrank ℚ (CellularFilteredGraphH1 ℚ F x) := by
  have hK := finrank_cellularFilteredGraphH1_add_vertices K F x
  have hQ := finrank_cellularFilteredGraphH1_add_vertices ℚ F x
  omega

theorem realOrdinaryH1Dim_eq_finrank_cellularFilteredGraphH1_of_active
    (K : Type*) [Field K] {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n)
    (hactive : realVerticesActive F x) :
    realOrdinaryH1Dim F x =
      Module.finrank K (CellularFilteredGraphH1 K F x) := by
  rw [realOrdinaryH1Dim, if_pos hactive,
    finrank_cellularFilteredGraphH1_field_independent K]

theorem realOrdinaryH1Dim_eq_zero_of_not_active
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n)
    (hactive : ¬ realVerticesActive F x) :
    realOrdinaryH1Dim F x = 0 := by
  simp [realOrdinaryH1Dim, hactive]

theorem realOrdinaryH1Dim_euler_of_active
    {m n : ℕ} (F : Simplex m → RealGrade n) (x : RealGrade n)
    (hactive : realVerticesActive F x) :
    (realOrdinaryH1Dim F x : ℤ) =
      (realActiveEdgeCount F x : ℤ) -
        Fintype.card (Vertex m) +
        (realOrdinaryH0Dim F x : ℤ) := by
  have heuler :=
    finrank_cellularFilteredGraphH1_add_vertices ℚ F x
  rw [← realOrdinaryH1Dim_eq_finrank_cellularFilteredGraphH1_of_active
    ℚ F x hactive] at heuler
  have hH0 : realOrdinaryH0Dim F x =
      Nat.card (realSublevelGraph F x).ConnectedComponent := by
    simp [realOrdinaryH0Dim, hactive]
  omega

/-- Split the active edge type into the central edge and the two arm
families. -/
def activeEdgeEquiv {m n : ℕ} (F : Simplex m → RealGrade n)
    (x : RealGrade n) :
    ActiveEdge F x ≃
      {u : Unit // realEdgeActive F x .e} ⊕
        ({j : Fin m // realEdgeActive F x (.a j)} ⊕
          {j : Fin m // realEdgeActive F x (.b j)}) where
  toFun e := by
    rcases e with ⟨e, he⟩
    cases e with
    | e => exact .inl ⟨(), he⟩
    | a j => exact .inr (.inl ⟨j, he⟩)
    | b j => exact .inr (.inr ⟨j, he⟩)
  invFun e := by
    cases e with
    | inl u => exact ⟨.e, u.2⟩
    | inr e =>
        cases e with
        | inl j => exact ⟨.a j.1, j.2⟩
        | inr j => exact ⟨.b j.1, j.2⟩
  left_inv e := by rcases e with ⟨e, he⟩; cases e <;> rfl
  right_inv e := by
    cases e with
    | inl u => rcases u with ⟨u, hu⟩; cases u; rfl
    | inr e =>
        cases e with
        | inl j => rcases j with ⟨j, hj⟩; rfl
        | inr j => rcases j with ⟨j, hj⟩; rfl

theorem realActiveEdgeCount_eq_central_add_arms {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    realActiveEdgeCount F x =
      Nat.card {u : Unit // realEdgeActive F x .e} +
        Nat.card {j : Fin m // realEdgeActive F x (.a j)} +
        Nat.card {j : Fin m // realEdgeActive F x (.b j)} := by
  rw [realActiveEdgeCount, Nat.card_congr (activeEdgeEquiv F x),
    Nat.card_sum, Nat.card_sum]
  omega

theorem realEdgeActive_realify_fGrade_e_iff (m : ℕ) (x : RealGrade 3) :
    realEdgeActive (realifyFiltration (fGrade m)) x .e ↔
      2 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  constructor
  · intro h
    exact ⟨by simpa [realEdgeActive, realifyFiltration, fGrade,
        RealGrade.LE, Grade.toReal] using h (0 : Fin 3),
      by simpa [realEdgeActive, realifyFiltration, fGrade,
        RealGrade.LE, Grade.toReal] using h (1 : Fin 3),
      by simpa [realEdgeActive, realifyFiltration, fGrade,
        RealGrade.LE, Grade.toReal] using h (2 : Fin 3)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;>
      simpa [realEdgeActive, realifyFiltration, fGrade,
        RealGrade.LE, Grade.toReal] using ‹_›

theorem realEdgeActive_realify_gGrade_e_iff (m : ℕ) (x : RealGrade 3) :
    realEdgeActive (realifyFiltration (gGrade m)) x .e ↔
      1 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  constructor
  · intro h
    exact ⟨by simpa [realEdgeActive, realifyFiltration, gGrade,
        RealGrade.LE, Grade.toReal] using h (0 : Fin 3),
      by simpa [realEdgeActive, realifyFiltration, gGrade,
        RealGrade.LE, Grade.toReal] using h (1 : Fin 3),
      by simpa [realEdgeActive, realifyFiltration, gGrade,
        RealGrade.LE, Grade.toReal] using h (2 : Fin 3)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;>
      simpa [realEdgeActive, realifyFiltration, gGrade,
        RealGrade.LE, Grade.toReal] using ‹_›

theorem lowerIndicator_origin_lastTwoCoordinates (x : RealGrade 3) :
    lowerIndicator (![0, 0] : RealGrade 2) (lastTwoCoordinates x) =
      if 0 ≤ x 1 ∧ 0 ≤ x 2 then 1 else 0 := by
  classical
  by_cases h : 0 ≤ x 1 ∧ 0 ≤ x 2
  · simp [lowerIndicator, lowerCoefficientHom, RealGrade.LE,
      lastTwoCoordinates, h]
  · simp [lowerIndicator, lowerCoefficientHom, RealGrade.LE,
      lastTwoCoordinates, h]

theorem realActiveEdgeCount_fGrade_sub_gGrade (m : ℕ)
    (x : RealGrade 3) :
    (realActiveEdgeCount (realifyFiltration (fGrade m)) x : ℤ) -
        (realActiveEdgeCount (realifyFiltration (gGrade m)) x : ℤ) =
      -slabIndicator (x 0) *
        lowerIndicator (![0, 0] : RealGrade 2)
          (lastTwoCoordinates x) := by
  classical
  rw [realActiveEdgeCount_eq_central_add_arms,
    realActiveEdgeCount_eq_central_add_arms]
  have ha :
      (fun j : Fin m ↦
        realEdgeActive (realifyFiltration (fGrade m)) x (.a j)) =
      (fun j : Fin m ↦
        realEdgeActive (realifyFiltration (gGrade m)) x (.a j)) := by
    funext j
    rfl
  have hb :
      (fun j : Fin m ↦
        realEdgeActive (realifyFiltration (fGrade m)) x (.b j)) =
      (fun j : Fin m ↦
        realEdgeActive (realifyFiltration (gGrade m)) x (.b j)) := by
    funext j
    rfl
  rw [ha, hb, lowerIndicator_origin_lastTwoCoordinates]
  by_cases hnonneg : 0 ≤ x 1 ∧ 0 ≤ x 2
  · by_cases h1 : 1 ≤ x 0
    · by_cases h2 : 2 ≤ x 0
      · simp [realEdgeActive_realify_fGrade_e_iff,
          realEdgeActive_realify_gGrade_e_iff, slabIndicator,
          hnonneg, h1, h2]
      · have hx2 : x 0 < 2 := lt_of_not_ge h2
        simp [realEdgeActive_realify_fGrade_e_iff,
          realEdgeActive_realify_gGrade_e_iff, slabIndicator,
          hnonneg, h1, h2, hx2]
    · have hx1 : x 0 < 1 := lt_of_not_ge h1
      have h2 : ¬ 2 ≤ x 0 := by linarith
      simp [realEdgeActive_realify_fGrade_e_iff,
        realEdgeActive_realify_gGrade_e_iff, slabIndicator,
        hnonneg, h1, h2, hx1]
  · simp [realEdgeActive_realify_fGrade_e_iff,
      realEdgeActive_realify_gGrade_e_iff, slabIndicator, hnonneg]

/-- Difference of the genuine cellular-`H₁` Hilbert functions for the same
two filtered graphs used in Theorem 1. -/
noncomputable def h1HilbertDifference (m : ℕ) (x : RealGrade 3) : ℤ :=
  (realOrdinaryH1Dim (realifyFiltration (fGrade m)) x : ℤ) -
    (realOrdinaryH1Dim (realifyFiltration (gGrade m)) x : ℤ)

theorem h1HilbertDifference_eq_h0_sub_euler_atom
    (m : ℕ) (x : RealGrade 3) :
    h1HilbertDifference m x =
      h0HilbertDifference m x -
        slabIndicator (x 0) *
          lowerIndicator (![0, 0] : RealGrade 2)
            (lastTwoCoordinates x) := by
  let F := realifyFiltration (fGrade m)
  let G := realifyFiltration (gGrade m)
  have hvertices : realVerticesActive F x ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
    simpa [F] using verticesActive_fGrade_iff m x
  have hverticesG : realVerticesActive G x ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
    simpa [G] using verticesActive_gGrade_iff m x
  by_cases hactive : realVerticesActive F x
  · have hcoords := hvertices.1 hactive
    have hactiveG : realVerticesActive G x := hverticesG.2 hcoords
    rw [h1HilbertDifference,
      realOrdinaryH1Dim_euler_of_active F x hactive,
      realOrdinaryH1Dim_euler_of_active G x hactiveG]
    simp only [F, G, realOrdinaryH0Dim_realify]
    change
      ((realActiveEdgeCount (realifyFiltration (fGrade m)) x : ℤ) -
          Fintype.card (Vertex m) +
          (ordinaryH0Dim (fGrade m) x : ℤ)) -
        ((realActiveEdgeCount (realifyFiltration (gGrade m)) x : ℤ) -
          Fintype.card (Vertex m) +
          (ordinaryH0Dim (gGrade m) x : ℤ)) =
        h0HilbertDifference m x -
          slabIndicator (x 0) *
            lowerIndicator (![0, 0] : RealGrade 2)
              (lastTwoCoordinates x)
    rw [h0HilbertDifference]
    linear_combination realActiveEdgeCount_fGrade_sub_gGrade m x
  · have hnotcoords : ¬ (0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2) := by
      exact fun h ↦ hactive (hvertices.2 h)
    have hactiveG : ¬ realVerticesActive G x := by
      exact fun h ↦ hnotcoords (hverticesG.1 h)
    rw [h1HilbertDifference,
      realOrdinaryH1Dim_eq_zero_of_not_active F x hactive,
      realOrdinaryH1Dim_eq_zero_of_not_active G x hactiveG]
    have hH0F : ordinaryH0Dim (fGrade m) x = 0 := by
      exact ordinaryH0Dim_eq_zero_of_not_active
        (fGrade m) x (by simpa [F] using hactive)
    have hH0G : ordinaryH0Dim (gGrade m) x = 0 := by
      exact ordinaryH0Dim_eq_zero_of_not_active
        (gGrade m) x (by simpa [G] using hactiveG)
    rw [h0HilbertDifference, hH0F, hH0G]
    by_cases hlast : 0 ≤ x 1 ∧ 0 ≤ x 2
    · have hx0 : ¬ 0 ≤ x 0 := by tauto
      have hx0' : x 0 < 1 := by linarith
      simp [lowerIndicator_origin_lastTwoCoordinates, hlast,
        slabIndicator, hx0']
    · simp [lowerIndicator_origin_lastTwoCoordinates, hlast]

/-- The Möbius measure of the cellular-`H₁` Hilbert-function difference.
It is the `H₀` measure with the Euler atom removed. -/
noncomputable def h1HilbertDifferenceMeasure (m : ℕ) :
    AtomicSignedMeasure 3 :=
  hilbertDifferenceMeasure m -
    AtomicSignedMeasure.tensor slabMeasure
      (atom (![0, 0] : RealGrade 2))

theorem cumulative_h1HilbertDifferenceMeasure (m : ℕ)
    (x : RealGrade 3) :
    cumulative (h1HilbertDifferenceMeasure m) x =
      h1HilbertDifference m x := by
  rw [h1HilbertDifferenceMeasure, cumulative_sub,
    cumulative_hilbertDifferenceMeasure,
    ← concat_first_last x, cumulative_tensor,
    cumulative_slabMeasure, cumulative_atom,
    h1HilbertDifference_eq_h0_sub_euler_atom]
  rfl

theorem h1HilbertDifferenceMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition (h1HilbertDifference m)
      (h1HilbertDifferenceMeasure m) :=
  cumulative_h1HilbertDifferenceMeasure m

/-- The `2m-1` positive (and negative) atoms remaining after the Euler atom
is removed: `m-1` corner atoms and `m` path atoms. -/
abbrev H1AtomIndex (m : ℕ) := Fin (m - 1) ⊕ Fin m

def h1AtomEmbedding (m : ℕ) :
    H1AtomIndex m → CounterexampleAtomIndex m
  | .inl j => .inl (.inr j)
  | .inr j => .inr j

theorem h1AtomEmbedding_injective (m : ℕ) :
    Function.Injective (h1AtomEmbedding m) := by
  intro i j h
  cases i <;> cases j <;> simp_all [h1AtomEmbedding]

def h1SourcePoint (m : ℕ) (i : H1AtomIndex m) : RealGrade 3 :=
  counterexampleSourcePoint m (h1AtomEmbedding m i)

def h1TargetPoint (m : ℕ) (i : H1AtomIndex m) : RealGrade 3 :=
  counterexampleTargetPoint m (h1AtomEmbedding m i)

theorem h1SourcePoint_injective (m : ℕ) :
    Function.Injective (h1SourcePoint m) :=
  (counterexampleSourcePoint_injective m).comp
    (h1AtomEmbedding_injective m)

theorem h1TargetPoint_injective (m : ℕ) :
    Function.Injective (h1TargetPoint m) :=
  (counterexampleTargetPoint_injective m).comp
    (h1AtomEmbedding_injective m)

theorem h1SourcePoint_ne_targetPoint {m : ℕ} (hm : 1 ≤ m)
    (i j : H1AtomIndex m) :
    h1SourcePoint m i ≠ h1TargetPoint m j :=
  counterexampleSourcePoint_ne_targetPoint hm
    (h1AtomEmbedding m i) (h1AtomEmbedding m j)

theorem one_le_h1_source_target_distance {m : ℕ} (hm : 1 ≤ m)
    (i j : H1AtomIndex m) :
    1 ≤ realL1Distance (h1SourcePoint m i) (h1TargetPoint m j) :=
  one_le_counterexample_source_target_distance hm
    (h1AtomEmbedding m i) (h1AtomEmbedding m j)

theorem h1_corresponding_distance (m : ℕ) (i : H1AtomIndex m) :
    realL1Distance (h1SourcePoint m i) (h1TargetPoint m i) = 1 :=
  counterexample_corresponding_distance m (h1AtomEmbedding m i)

theorem card_H1AtomIndex {m : ℕ} (hm : 1 ≤ m) :
    Fintype.card (H1AtomIndex m) = 2 * m - 1 := by
  simp [H1AtomIndex]
  omega

theorem h1_unitAtomicKR1 (m : ℕ) (hm : 1 ≤ m) :
    unitAtomicKR1 (h1SourcePoint m) (h1TargetPoint m) =
      2 * m - 1 := by
  rw [unitAtomicKR1_eq_card_of_separated_unit_matching
    _ _ (one_le_h1_source_target_distance hm)
    (h1_corresponding_distance m), card_H1AtomIndex hm]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
  norm_num

noncomputable def h1CornerMeasure (m : ℕ) : AtomicSignedMeasure 2 :=
  ∑ j ∈ Finset.range (m - 1), atom (cornerPointNat m j)

noncomputable def h1PathMeasure (m : ℕ) : AtomicSignedMeasure 2 :=
  ∑ j ∈ Finset.range m, atom (pathPointNat m j)

noncomputable def h1PositiveMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (atom ![1]) (h1CornerMeasure m) +
    AtomicSignedMeasure.tensor (atom ![2]) (h1PathMeasure m)

noncomputable def h1NegativeMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor (atom ![1]) (h1PathMeasure m) +
    AtomicSignedMeasure.tensor (atom ![2]) (h1CornerMeasure m)

theorem staircaseMeasure_sub_origin_eq_h1Corner_sub_h1Path (m : ℕ) :
    staircaseMeasure m - atom (![0, 0] : RealGrade 2) =
      h1CornerMeasure m - h1PathMeasure m := by
  rw [staircaseMeasure_eq_positive_sub_negative]
  simp only [staircasePositiveMeasure, staircaseNegativeMeasure,
    h1CornerMeasure, h1PathMeasure]
  abel

theorem h1HilbertDifferenceMeasure_eq_positive_sub_negative (m : ℕ) :
    h1HilbertDifferenceMeasure m =
      h1PositiveMeasure m - h1NegativeMeasure m := by
  rw [h1HilbertDifferenceMeasure, hilbertDifferenceMeasure,
    ← AtomicSignedMeasure.tensor_sub_right,
    staircaseMeasure_sub_origin_eq_h1Corner_sub_h1Path,
    slabMeasure, AtomicSignedMeasure.tensor_sub_left,
    AtomicSignedMeasure.tensor_sub_right,
    AtomicSignedMeasure.tensor_sub_right]
  simp only [h1PositiveMeasure, h1NegativeMeasure]
  abel

theorem sum_h1SourcePoint_atoms (m : ℕ) :
    (∑ i : H1AtomIndex m, atom (h1SourcePoint m i)) =
      h1PositiveMeasure m := by
  classical
  have hcorner :
      (∑ j : Fin (m - 1), atom (h1SourcePoint m (.inl j))) =
        ∑ j ∈ Finset.range (m - 1),
          atom (concatGrade ![1] (cornerPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, h1SourcePoint, h1AtomEmbedding,
      counterexampleSourcePoint, counterexampleSourceInteger,
      staircasePositiveInteger, prependInteger_toReal,
      cornerPointInteger_toReal]
  have hpath :
      (∑ j : Fin m, atom (h1SourcePoint m (.inr j))) =
        ∑ j ∈ Finset.range m,
          atom (concatGrade ![2] (pathPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, h1SourcePoint, h1AtomEmbedding,
      counterexampleSourcePoint, counterexampleSourceInteger,
      staircaseNegativeInteger, prependInteger_toReal,
      pathPointInteger_toReal]
  rw [Fintype.sum_sum_type, hcorner, hpath]
  simp only [h1PositiveMeasure, h1CornerMeasure, h1PathMeasure,
    AtomicSignedMeasure.tensor_finset_sum_right,
    AtomicSignedMeasure.tensor_atom_atom]

theorem sum_h1TargetPoint_atoms (m : ℕ) :
    (∑ i : H1AtomIndex m, atom (h1TargetPoint m i)) =
      h1NegativeMeasure m := by
  classical
  have hcorner :
      (∑ j : Fin (m - 1), atom (h1TargetPoint m (.inl j))) =
        ∑ j ∈ Finset.range (m - 1),
          atom (concatGrade ![2] (cornerPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, h1TargetPoint, h1AtomEmbedding,
      counterexampleTargetPoint, counterexampleTargetInteger,
      staircasePositiveInteger, prependInteger_toReal,
      cornerPointInteger_toReal]
  have hpath :
      (∑ j : Fin m, atom (h1TargetPoint m (.inr j))) =
        ∑ j ∈ Finset.range m,
          atom (concatGrade ![1] (pathPointNat m j)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, h1TargetPoint, h1AtomEmbedding,
      counterexampleTargetPoint, counterexampleTargetInteger,
      staircaseNegativeInteger, prependInteger_toReal,
      pathPointInteger_toReal]
  rw [Fintype.sum_sum_type, hcorner, hpath]
  simp only [h1NegativeMeasure, h1CornerMeasure, h1PathMeasure,
    AtomicSignedMeasure.tensor_finset_sum_right,
    AtomicSignedMeasure.tensor_atom_atom]
  abel

theorem h1HilbertDifferenceMeasure_eq_indexed_jordan (m : ℕ) :
    h1HilbertDifferenceMeasure m =
      (∑ i : H1AtomIndex m, atom (h1SourcePoint m i)) -
        ∑ i : H1AtomIndex m, atom (h1TargetPoint m i) := by
  rw [sum_h1SourcePoint_atoms, sum_h1TargetPoint_atoms,
    h1HilbertDifferenceMeasure_eq_positive_sub_negative]

theorem h1_isUnitAtomicJordanRepresentation (m : ℕ) (hm : 1 ≤ m) :
    IsUnitAtomicJordanRepresentation (h1HilbertDifferenceMeasure m)
      (h1SourcePoint m) (h1TargetPoint m) :=
  ⟨h1SourcePoint_injective m, h1TargetPoint_injective m,
    h1SourcePoint_ne_targetPoint hm,
    h1HilbertDifferenceMeasure_eq_indexed_jordan m⟩

theorem h1HilbertDifferenceMeasure_KR1 (m : ℕ) (hm : 1 ≤ m) :
    (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.posPart =
        unitAtomMeasure (h1SourcePoint m) ∧
      (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.negPart =
        unitAtomMeasure (h1TargetPoint m) ∧
      unitAtomicKR1 (h1SourcePoint m) (h1TargetPoint m) = 2 * m - 1 := by
  let hJordan := h1_isUnitAtomicJordanRepresentation m hm
  exact ⟨hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure, h1_unitAtomicKR1 m hm⟩

theorem h1HilbertDifferenceMeasure_measureKR1 (m : ℕ) (hm : 1 ≤ m) :
    measureKR1
        (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.posPart
        (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.negPart =
      (2 * m - 1 : ℕ) := by
  let hJordan := h1_isUnitAtomicJordanRepresentation m hm
  rw [hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    measureKR1_eq_card_of_separated_unit_matching
      (h1SourcePoint m) (h1TargetPoint m)
      (one_le_h1_source_target_distance hm)
      (h1_corresponding_distance m),
    card_H1AtomIndex hm]

/-- Difference of the Euler-characteristic Hilbert functions,
`Δχ = Δβ₀ - Δβ₁`. -/
noncomputable def eulerHilbertDifference (m : ℕ)
    (x : RealGrade 3) : ℤ :=
  h0HilbertDifference m x - h1HilbertDifference m x

/-- Only the single Euler atom survives the cancellation between `H₀` and
`H₁`. -/
noncomputable def eulerHilbertDifferenceMeasure :
    AtomicSignedMeasure 3 :=
  AtomicSignedMeasure.tensor slabMeasure
    (atom (![0, 0] : RealGrade 2))

theorem eulerHilbertDifference_eq_slab_origin
    (m : ℕ) (x : RealGrade 3) :
    eulerHilbertDifference m x =
      slabIndicator (x 0) *
        lowerIndicator (![0, 0] : RealGrade 2)
          (lastTwoCoordinates x) := by
  rw [eulerHilbertDifference,
    h1HilbertDifference_eq_h0_sub_euler_atom]
  ring

theorem cumulative_eulerHilbertDifferenceMeasure
    (m : ℕ) (x : RealGrade 3) :
    cumulative eulerHilbertDifferenceMeasure x =
      eulerHilbertDifference m x := by
  rw [← concat_first_last x, eulerHilbertDifferenceMeasure,
    cumulative_tensor, cumulative_slabMeasure, cumulative_atom,
    eulerHilbertDifference_eq_slab_origin]
  rfl

theorem eulerHilbertDifferenceMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition (eulerHilbertDifference m)
      eulerHilbertDifferenceMeasure :=
  cumulative_eulerHilbertDifferenceMeasure m

def eulerSourcePoint (_ : Unit) : RealGrade 3 :=
  ![1, 0, 0]

def eulerTargetPoint (_ : Unit) : RealGrade 3 :=
  ![2, 0, 0]

theorem eulerSourcePoint_ne_targetPoint (i j : Unit) :
    eulerSourcePoint i ≠ eulerTargetPoint j := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  norm_num [eulerSourcePoint, eulerTargetPoint] at h0

theorem euler_corresponding_distance (i : Unit) :
    realL1Distance (eulerSourcePoint i) (eulerTargetPoint i) = 1 := by
  cases i
  norm_num [eulerSourcePoint, eulerTargetPoint,
    realL1Distance, Fin.sum_univ_succ]

theorem eulerHilbertDifferenceMeasure_eq_indexed_jordan :
    eulerHilbertDifferenceMeasure =
      (∑ i : Unit, atom (eulerSourcePoint i)) -
        ∑ i : Unit, atom (eulerTargetPoint i) := by
  rw [eulerHilbertDifferenceMeasure, slabMeasure,
    AtomicSignedMeasure.tensor_sub_left]
  simp only [AtomicSignedMeasure.tensor_atom_atom,
    Fintype.sum_unique]
  have hsource :
      concatGrade ![1] (![0, 0] : RealGrade 2) =
        eulerSourcePoint () := by
    funext i
    fin_cases i <;> rfl
  have htarget :
      concatGrade ![2] (![0, 0] : RealGrade 2) =
        eulerTargetPoint () := by
    funext i
    fin_cases i <;> rfl
  rw [hsource, htarget]

theorem euler_isUnitAtomicJordanRepresentation :
    IsUnitAtomicJordanRepresentation eulerHilbertDifferenceMeasure
      eulerSourcePoint eulerTargetPoint :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ _ _ ↦ Subsingleton.elim _ _,
    eulerSourcePoint_ne_targetPoint,
    eulerHilbertDifferenceMeasure_eq_indexed_jordan⟩

theorem euler_unitAtomicKR1 :
    unitAtomicKR1 eulerSourcePoint eulerTargetPoint = 1 := by
  rw [unitAtomicKR1_eq_card_of_separated_unit_matching
    eulerSourcePoint eulerTargetPoint
    (fun i j ↦ by
      cases i
      cases j
      rw [euler_corresponding_distance]
    )
    euler_corresponding_distance]
  norm_num

theorem eulerHilbertDifferenceMeasure_KR1 :
    eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.posPart =
        unitAtomMeasure eulerSourcePoint ∧
      eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.negPart =
        unitAtomMeasure eulerTargetPoint ∧
      unitAtomicKR1 eulerSourcePoint eulerTargetPoint = 1 := by
  let hJordan := euler_isUnitAtomicJordanRepresentation
  exact ⟨hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure, euler_unitAtomicKR1⟩

theorem eulerHilbertDifferenceMeasure_measureKR1 :
    measureKR1
        eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.posPart
        eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.negPart =
      1 := by
  let hJordan := euler_isUnitAtomicJordanRepresentation
  rw [hJordan.posPart_eq_unitAtomMeasure,
    hJordan.negPart_eq_unitAtomMeasure,
    measureKR1_eq_card_of_separated_unit_matching
      eulerSourcePoint eulerTargetPoint
      (fun i j ↦ by
        cases i
        cases j
        rw [euler_corresponding_distance])
      euler_corresponding_distance]
  norm_num

/-! ### Separate `H₁` Hilbert measures for the two filtrations -/

/-- Möbius measure of the active-edge counting function. -/
noncomputable def edgeGradeMeasure {m n : ℕ}
    (F : Simplex m → RealGrade n) : AtomicSignedMeasure n :=
  ∑ e : Edge m, atom (F (.edge e))

theorem cumulative_edgeGradeMeasure {m n : ℕ}
    (F : Simplex m → RealGrade n) (x : RealGrade n) :
    cumulative (edgeGradeMeasure F) x =
      (realActiveEdgeCount F x : ℤ) := by
  classical
  have hindicator (e : Edge m) :
      lowerIndicator (F (.edge e)) x =
        if realEdgeActive F x e then (1 : ℤ) else 0 := by
    by_cases hactive : realEdgeActive F x e
    · have hle : RealGrade.LE (F (.edge e)) x := hactive
      have hone : lowerIndicator (F (.edge e)) x = 1 := by
        simpa [lowerIndicator] using
          lowerCoefficientHom_apply_of_le (F (.edge e)) x 1 hle
      simp [hone, hactive]
    · have hnle : ¬ RealGrade.LE (F (.edge e)) x := hactive
      have hzero : lowerIndicator (F (.edge e)) x = 0 := by
        simpa [lowerIndicator] using
          lowerCoefficientHom_apply_of_not_le (F (.edge e)) x 1 hnle
      simp [hzero, hactive]
  rw [edgeGradeMeasure, cumulative_fintype_sum]
  simp_rw [cumulative_atom, hindicator]
  rw [realActiveEdgeCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simpa only [Finset.sum_boole]

theorem realActiveEdgeCount_eq_zero_of_not_verticesActive
    {m n : ℕ} {F : Simplex m → RealGrade n}
    (hF : RealMonotoneFiltration F)
    (hvertices : ∀ v : Vertex m,
      F (.vertex v) = F (.vertex (.s : Vertex m)))
    (x : RealGrade n) (hactive : ¬ realVerticesActive F x) :
    realActiveEdgeCount F x = 0 := by
  classical
  rw [realActiveEdgeCount, Nat.card_eq_fintype_card,
    Fintype.card_eq_zero_iff]
  refine ⟨fun active ↦ ?_⟩
  rcases active with ⟨e, he⟩
  have hsource : edgeSource e ∈ endpoints e := by
    cases e <;> simp [edgeSource, endpoints]
  have hvertexEdge := hF e (edgeSource e) hsource
  apply hactive
  intro i
  rw [← hvertices (edgeSource e)]
  exact (hvertexEdge i).trans (he i)

/-- For a graph filtration with a common vertex grade, Euler--Poincaré
constructs the separate `H₁` Hilbert measure from the `H₀` measure, the edge
grades, and the vertex Euler term. -/
noncomputable def cellularH1Measure {m n : ℕ}
    (F : Simplex m → RealGrade n) (muH0 : AtomicSignedMeasure n) :
    AtomicSignedMeasure n :=
  muH0 + edgeGradeMeasure F -
    (Fintype.card (Vertex m) : ℤ) • atom (F (.vertex .s))

theorem cellularH1Measure_isHilbertDecomposition
    {m n : ℕ} {F : Simplex m → RealGrade n}
    {muH0 : AtomicSignedMeasure n}
    (hF : RealMonotoneFiltration F)
    (hvertices : ∀ v : Vertex m,
      F (.vertex v) = F (.vertex (.s : Vertex m)))
    (hmuH0 : IsHilbertDecomposition
      (fun x ↦ (realOrdinaryH0Dim F x : ℤ)) muH0) :
    IsHilbertDecomposition
      (fun x ↦ (realOrdinaryH1Dim F x : ℤ))
      (cellularH1Measure F muH0) := by
  intro x
  rw [cellularH1Measure, cumulative_sub, cumulative_add,
    hmuH0, cumulative_edgeGradeMeasure, cumulative_smul,
    cumulative_atom]
  change (realOrdinaryH0Dim F x : ℤ) +
      (realActiveEdgeCount F x : ℤ) -
      (Fintype.card (Vertex m) : ℤ) *
        lowerIndicator (F (.vertex .s)) x =
    (realOrdinaryH1Dim F x : ℤ)
  by_cases hactive : realVerticesActive F x
  · rw [realOrdinaryH1Dim_euler_of_active F x hactive]
    have hlower :
        lowerIndicator (F (.vertex (.s : Vertex m))) x = 1 := by
      simpa [lowerIndicator] using
        lowerCoefficientHom_apply_of_le
          (F (.vertex (.s : Vertex m))) x 1 hactive
    rw [hlower]
    ring
  · rw [realOrdinaryH1Dim_eq_zero_of_not_active F x hactive,
      realOrdinaryH0Dim_eq_zero_of_not_active F x hactive,
      realActiveEdgeCount_eq_zero_of_not_verticesActive
        hF hvertices x hactive]
    have hlower :
        lowerIndicator (F (.vertex (.s : Vertex m))) x = 0 := by
      simpa [lowerIndicator] using
        lowerCoefficientHom_apply_of_not_le
          (F (.vertex (.s : Vertex m))) x 1 hactive
    rw [hlower]
    simp

noncomputable def h1FMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  cellularH1Measure (realifyFiltration (fGrade m)) (h0FMeasure m)

noncomputable def h1GMeasure (m : ℕ) : AtomicSignedMeasure 3 :=
  cellularH1Measure (realifyFiltration (gGrade m)) (h0GMeasure m)

theorem h1FMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition
      (fun x ↦
        (realOrdinaryH1Dim (realifyFiltration (fGrade m)) x : ℤ))
      (h1FMeasure m) := by
  apply cellularH1Measure_isHilbertDecomposition
    (realifyFiltration_monotone (fGrade_monotone m))
  · intro v
    rfl
  · exact h0FMeasure_isHilbertDecomposition m

theorem h1GMeasure_isHilbertDecomposition (m : ℕ) :
    IsHilbertDecomposition
      (fun x ↦
        (realOrdinaryH1Dim (realifyFiltration (gGrade m)) x : ℤ))
      (h1GMeasure m) := by
  apply cellularH1Measure_isHilbertDecomposition
    (realifyFiltration_monotone (gGrade_monotone m))
  · intro v
    rfl
  · exact h0GMeasure_isHilbertDecomposition m

theorem h1FMeasure_sub_h1GMeasure (m : ℕ) :
    h1FMeasure m - h1GMeasure m =
      h1HilbertDifferenceMeasure m := by
  apply IsHilbertDecomposition.unique
    (h := h1HilbertDifference m)
  · intro x
    rw [cumulative_sub, h1FMeasure_isHilbertDecomposition,
      h1GMeasure_isHilbertDecomposition]
    rfl
  · exact h1HilbertDifferenceMeasure_isHilbertDecomposition m

theorem h1HilbertDifferenceSignedMeasure_eq_sub (m : ℕ) :
    (h1HilbertDifferenceMeasure m).toSignedMeasure =
      (h1FMeasure m).toSignedMeasure -
        (h1GMeasure m).toSignedMeasure := by
  rw [← AtomicSignedMeasure.toSignedMeasure_sub,
    h1FMeasure_sub_h1GMeasure]

/-- Same-family `H₁`/Euler proposition.  The `H₁` function is defined from
the kernel of the actual cellular boundary, its two separate Hilbert signed
measures have the displayed difference with exact `KR₁ = 2m-1`, and
subtracting it from the `H₀` difference leaves one unit-cost Euler atom. -/
theorem same_family_H1_and_Euler_cancellation
    (m : ℕ) (hm : 1 ≤ m) :
    IsHilbertDecomposition
        (fun x ↦
          (realOrdinaryH1Dim (realifyFiltration (fGrade m)) x : ℤ))
        (h1FMeasure m) ∧
      IsHilbertDecomposition
        (fun x ↦
          (realOrdinaryH1Dim (realifyFiltration (gGrade m)) x : ℤ))
        (h1GMeasure m) ∧
      h1HilbertDifferenceMeasure m = h1FMeasure m - h1GMeasure m ∧
      (h1HilbertDifferenceMeasure m).toSignedMeasure =
        (h1FMeasure m).toSignedMeasure -
          (h1GMeasure m).toSignedMeasure ∧
      IsHilbertDecomposition (h1HilbertDifference m)
        (h1HilbertDifferenceMeasure m) ∧
      IsUnitAtomicJordanRepresentation (h1HilbertDifferenceMeasure m)
        (h1SourcePoint m) (h1TargetPoint m) ∧
      (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.posPart =
        unitAtomMeasure (h1SourcePoint m) ∧
      (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.negPart =
        unitAtomMeasure (h1TargetPoint m) ∧
      unitAtomicKR1 (h1SourcePoint m) (h1TargetPoint m) = 2 * m - 1 ∧
      measureKR1
          (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.posPart
          (h1HilbertDifferenceMeasure m).toSignedMeasure.toJordanDecomposition.negPart =
        (2 * m - 1 : ℕ) ∧
      IsHilbertDecomposition (eulerHilbertDifference m)
        eulerHilbertDifferenceMeasure ∧
      IsUnitAtomicJordanRepresentation eulerHilbertDifferenceMeasure
        eulerSourcePoint eulerTargetPoint ∧
      eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.posPart =
        unitAtomMeasure eulerSourcePoint ∧
      eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.negPart =
        unitAtomMeasure eulerTargetPoint ∧
      unitAtomicKR1 eulerSourcePoint eulerTargetPoint = 1 ∧
      measureKR1
          eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.posPart
          eulerHilbertDifferenceMeasure.toSignedMeasure.toJordanDecomposition.negPart =
        1 := by
  let hH1Jordan := h1_isUnitAtomicJordanRepresentation m hm
  let hEulerJordan := euler_isUnitAtomicJordanRepresentation
  exact ⟨h1FMeasure_isHilbertDecomposition m,
    h1GMeasure_isHilbertDecomposition m,
    (h1FMeasure_sub_h1GMeasure m).symm,
    h1HilbertDifferenceSignedMeasure_eq_sub m,
    h1HilbertDifferenceMeasure_isHilbertDecomposition m,
    hH1Jordan, hH1Jordan.posPart_eq_unitAtomMeasure,
    hH1Jordan.negPart_eq_unitAtomMeasure, h1_unitAtomicKR1 m hm,
    h1HilbertDifferenceMeasure_measureKR1 m hm,
    eulerHilbertDifferenceMeasure_isHilbertDecomposition m,
    hEulerJordan, hEulerJordan.posPart_eq_unitAtomMeasure,
    hEulerJordan.negPart_eq_unitAtomMeasure, euler_unitAtomicKR1,
    eulerHilbertDifferenceMeasure_measureKR1⟩


end OneEdgeInstability.P1
