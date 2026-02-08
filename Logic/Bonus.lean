/- If you have not used any of Lean/Rocq/etc before, this file may be confusing to you and my advice
   is to look away.

   It defines an embedding of propositional logic in Lean, where And, Or, etc. are constructors of
   the Expression (inductive) type. This is in contrast with Lean's definition of the connectives,
   as these work directly with the Prop type. We are doing propositional logic here, so we want
   something much more limited. Many metatheorems that are true about propositional logic are not
   true or not provable in Lean's higher-order logic (e.g., being a tautology is decidable in
   propositional logic). This file does not define explicit inference rules, though we could use an
   inductively defined proposition or such for that purpose (this would make induction proofs on
   inference rules possible). You may recognize some of the lemmas below as exercises from the first
   problem sheet.

   We may compare the natural deduction calculus we are studying to Peano's axioms for natural
   numbers: we would not use those to compute anything in real life, but they are very convenient
   for reasoning about the core properties of natural numbers. Similarly, we use a simple calculus
   for natural deduction because we are not striving to make a deductive system that is
   user-friendly, but one that is nice to reason about. Natural deduction came about because people
   wanted to map out the boundaries of deduction and answer some deep questions about the nature of
   computation. Such hard questions are easier to answer for a barebones calculus than for a
   full-fledged industrial system; Lean and our simpler natural deduction calculus are optimized for
   different metrics. Note that a way of "verifying" Lean would be to show that it is equivalent to
   a similarly barebones calculus, for some appropriate notion of equivalence (see for instance
   https://inria.hal.science/hal-01094195 for the core calculus implemented by the Rocq proof
   assistant, and https://metarocq.github.io/ for a formalization of Rocq within Rocq - Lean's
   foundations are very close to those). In a way, the calculus is a specification, and a
   specification should be as simple as it can be, so as to minimize the chances for bugs to creep
   in.

   There are some tools for showing proof trees in proof assistants (including Lean). See
   https://paperproof.brick.do/lean-coq-isabel-and-their-proof-trees-yjnd2O2RgxwV for a comparison.
 -/

import Lean.Data.AssocList
import Mathlib.Tactic.Ring

def ContextT := Lean.AssocList String Bool
@[simp] def empty_context   : ContextT := List.toAssocList' []
@[simp] def sample_context₁ : ContextT := List.toAssocList' [("p₀", true), ("p₁", false)]
@[simp] def sample_context₂ : ContextT :=
  List.toAssocList'
    [("p₀", true), ("p₁", false), ("p₂", false), ("p₃", false), ("p₄", false), ("p₅", false)]

inductive Expression where
| And  (e₁ e₂: Expression)
| Or   (e₁ e₂: Expression)
| Impl (e₁ e₂: Expression)
| Not  (e    : Expression)
| Iff  (e₁ e₂: Expression)
| False
| Var (name: String)
open Expression
deriving instance DecidableEq for Expression

@[simp]
def is_context_appropriate (c: ContextT) (e: Expression) : Bool :=
  match e with
  | .And  e₁ e₂ => is_context_appropriate c e₁ && is_context_appropriate c e₂
  | .Or   e₁ e₂ => is_context_appropriate c e₁ && is_context_appropriate c e₂
  | .Impl e₁ e₂ => is_context_appropriate c e₁ && is_context_appropriate c e₂
  | .Not  e     => is_context_appropriate c e
  | .Iff  e₁ e₂ => is_context_appropriate c e₁ && is_context_appropriate c e₂
  | .False      => true
  | .Var name   => Lean.AssocList.contains name c

/- Not in the standard library for some weird reason -/
lemma ListAssoc_contains_impl_ListAssoc_find_successful:
  ∀{K V: Type} [BEq K] (al: Lean.AssocList K V) (k: K),
  al.contains k = true → ∃v, al.find? k = some v
:= by
  intro K V BEqK al k contains
  induction al with
  | nil => unfold Lean.AssocList.contains at contains; simp at contains
  | cons k' v' tail tail_ih =>
    simp [Lean.AssocList.find?]
    generalize h: (k' == k) = b
    cases b
    . simp; unfold Lean.AssocList.contains at contains; simp at contains
      obtain head_case | tail_case := contains
      . simp [h] at head_case
      . apply tail_ih at tail_case
        obtain ⟨v, hv⟩ := tail_case
        exists v
    . simp

@[simp]
def eval_expr_prop?_aux (e: Expression) : (String → Option Prop) → Option Prop :=
  fun lookup =>
    match e with
    | .And e₁ e₂ =>
      let p₁ := eval_expr_prop?_aux e₁ lookup
      let p₂ := eval_expr_prop?_aux e₂ lookup
      match p₁, p₂ with
      | some p₁, some p₂ => some (p₁ ∧ p₂)
      | _, _ => none
    | .Or e₁ e₂ =>
      let p₁ := eval_expr_prop?_aux e₁ lookup
      let p₂ := eval_expr_prop?_aux e₂ lookup
      match p₁, p₂ with
      | some p₁, some p₂ => some (p₁ ∨ p₂)
      | _, _ => none
    | .Impl e₁ e₂ =>
      let p₁ := eval_expr_prop?_aux e₁ lookup
      let p₂ := eval_expr_prop?_aux e₂ lookup
      match p₁, p₂ with
      | some p₁, some p₂ => some (p₁ → p₂)
      | _, _ => none
    | .Not e =>
      let p := eval_expr_prop?_aux e lookup
      match p with
      | some p => some (¬p)
      | _ => none
    | .Iff  e₁ e₂ =>
      let p₁ := eval_expr_prop?_aux e₁ lookup
      let p₂ := eval_expr_prop?_aux e₂ lookup
      match p₁, p₂ with
      | some p₁, some p₂ => some (p₁ ↔ p₂)
      | _, _ => none
    | .False => some ⊥
    | .Var name => lookup name

@[simp]
def eval_expr_prop? (e: Expression) (c: ContextT) : Option Prop :=
  eval_expr_prop?_aux
    e
    (fun name =>
      match Lean.AssocList.find? name c with
      | some true  => some True
      | some false => some False
      | none       => none)

lemma eval_expr_prop?_in_appropriate_context_is_some:
  ∀(e: Expression) (c: ContextT),
  is_context_appropriate c e → ∃p, eval_expr_prop? e c = some p
:= by
  intro e c c_ok
  unfold eval_expr_prop?
  induction e with
  | And e₁ e₂ ih₁ ih₂ =>
    have c_ok₁ : is_context_appropriate c e₁ := by simp at c_ok; lia
    have c_ok₂ : is_context_appropriate c e₂ := by simp at c_ok; lia
    apply ih₁ at c_ok₁; obtain ⟨p₁, hp₁⟩ := c_ok₁
    apply ih₂ at c_ok₂; obtain ⟨p₂, hp₂⟩ := c_ok₂
    exists (p₁ ∧ p₂); simp; grind
  | Or e₁ e₂ ih₁ ih₂ =>
    have c_ok₁ : is_context_appropriate c e₁ := by simp at c_ok; lia
    have c_ok₂ : is_context_appropriate c e₂ := by simp at c_ok; lia
    apply ih₁ at c_ok₁; obtain ⟨p₁, hp₁⟩ := c_ok₁
    apply ih₂ at c_ok₂; obtain ⟨p₂, hp₂⟩ := c_ok₂
    exists (p₁ ∨ p₂); simp; grind
  | Impl e₁ e₂ ih₁ ih₂ =>
    have c_ok₁ : is_context_appropriate c e₁ := by simp at c_ok; lia
    have c_ok₂ : is_context_appropriate c e₂ := by simp at c_ok; lia
    apply ih₁ at c_ok₁; obtain ⟨p₁, hp₁⟩ := c_ok₁
    apply ih₂ at c_ok₂; obtain ⟨p₂, hp₂⟩ := c_ok₂
    exists (p₁ → p₂); simp; grind
  | Not e ih =>
    have c_ok : is_context_appropriate c e := by simp at c_ok; lia
    apply ih at c_ok; obtain ⟨p, hp⟩ := c_ok
    exists (¬p); simp; grind
  | Iff e₁ e₂ ih₁ ih₂ =>
    have c_ok₁ : is_context_appropriate c e₁ := by simp at c_ok; lia
    have c_ok₂ : is_context_appropriate c e₂ := by simp at c_ok; lia
    apply ih₁ at c_ok₁; obtain ⟨p₁, hp₁⟩ := c_ok₁
    apply ih₂ at c_ok₂; obtain ⟨p₂, hp₂⟩ := c_ok₂
    exists (p₁ ↔ p₂); simp; grind
  | False => exists ⊥
  | Var name =>
    simp at c_ok; simp; apply ListAssoc_contains_impl_ListAssoc_find_successful at c_ok
    obtain ⟨v, hv⟩ := c_ok
    exists v; grind

@[simp]
def eval_expr_prop (e: Expression) (c: ContextT) (c_ok: is_context_appropriate c e): Prop := by
  generalize hpo : eval_expr_prop? e c = po
  match po with
  | some x => apply x
  | none =>
    have hx: ∃x, eval_expr_prop? e c = some x := by
      apply eval_expr_prop?_in_appropriate_context_is_some e c c_ok
    rw [hpo] at hx; simp at hx

section Exercise1
  @[simp] def Tree₁ : Expression := Not (Not (Not (False)))
  @[simp] def Tree₂ : Expression :=
    Impl
      (Impl (Var "p₀") False)
      (And
        (Iff (Var "p₀") (Var "p₁"))
        (Var "p₅")
      )
  @[simp] def Tree₃ : Expression :=
    Not
      (Impl
        (Not (Var "p₁"))
        (Not (Var "p₁"))
      )

  lemma context_appropriate₂ : is_context_appropriate sample_context₂ Tree₂ = true := by
    simp [List.toAssocList', Lean.AssocList.contains]
  #reduce eval_expr_prop Tree₂ sample_context₂ context_appropriate₂

  def a : Option Prop := by
    generalize hbase : eval_expr_prop? Tree₂ sample_context₂ = base
    simp at hbase
    /- simp only [ -/
    /-   eval_expr_prop, Tree₂, BEq.beq, decide, Decidable.rec, sample_context₂, Lean.AssocList.find?, -/
    /-   List.toAssocList', instDecidableEqString -/
    /- ] -/
    apply base
end Exercise1

section Subformulae
  inductive is_subformula_prop: Expression → Expression → Prop where
  | SF_Self {e: Expression}: is_subformula_prop e e
  | SF_And_left {sf e₁ e₂: Expression}:
    is_subformula_prop e₁ sf → is_subformula_prop (And e₁ e₂) sf
  | SF_And_right {sf e₁ e₂: Expression}:
    is_subformula_prop e₂ sf → is_subformula_prop (And e₁ e₂) sf
  | SF_Or_left {sf e₁ e₂: Expression}:
    is_subformula_prop e₁ sf → is_subformula_prop (Or e₁ e₂) sf
  | SF_Or_right {sf e₁ e₂: Expression}:
    is_subformula_prop e₂ sf → is_subformula_prop (Or e₁ e₂) sf
  | SF_Impl_left {sf e₁ e₂: Expression}:
    is_subformula_prop e₁ sf → is_subformula_prop (Impl e₁ e₂) sf
  | SF_Impl_right {sf e₁ e₂: Expression}:
    is_subformula_prop e₂ sf → is_subformula_prop (Impl e₁ e₂) sf
  | SF_Not {sf e: Expression}: is_subformula_prop e sf → is_subformula_prop (Not e) sf
  | SF_Iff_left {sf e₁ e₂: Expression}:
    is_subformula_prop e₁ sf → is_subformula_prop (Iff e₁ e₂) sf
  | SF_Iff_right {sf e₁ e₂: Expression}:
    is_subformula_prop e₂ sf → is_subformula_prop (Iff e₁ e₂) sf
  open is_subformula_prop

  @[simp]
  def is_subformula (e sf: Expression) : Bool :=
    if e = sf then true else
    match e with
    | .And  e₁' e₂' => is_subformula e₁' sf || is_subformula e₂' sf
    | .Or   e₁' e₂' => is_subformula e₁' sf || is_subformula e₂' sf
    | .Not  e'      => is_subformula e'  sf
    | .Impl e₁' e₂' => is_subformula e₁' sf || is_subformula e₂' sf
    | .Iff  e₁' e₂' => is_subformula e₁' sf || is_subformula e₂' sf
    | _ => false

  section Exercise₂
    def is_subformula_prop_is_transitive:
      ∀(e₁ e₂ e₃: Expression),
      is_subformula_prop e₁ e₂ → is_subformula_prop e₂ e₃ → is_subformula_prop e₁ e₃
    := by
      intro e₁ e₂ e₃ e₂_sf_e₁ e₃_sf_e₂
      induction e₁ with
      | And e₁' e₂' ih₁ ih₂ =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
        | SF_And_left  a => apply SF_And_left ; apply ih₁ ahttps://metarocq.github.io/https://metarocq.github.io/
        | SF_And_right a => apply SF_And_right; apply ih₂ a
      | Or e₁' e₂' ih₁ ih₂ =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
        | SF_Or_left  a => apply SF_Or_left ; apply ih₁ a
        | SF_Or_right a => apply SF_Or_right; apply ih₂ a
      | Not e ih =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
        | SF_Not a => apply SF_Not; apply ih a
      | Impl e₁' e₂' ih₁ ih₂ =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
        | SF_Impl_left  a => apply SF_Impl_left ; apply ih₁ a
        | SF_Impl_right a => apply SF_Impl_right; apply ih₂ a
      | Iff e₁' e₂' ih₁ ih₂ =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
        | SF_Iff_left  a => apply SF_Iff_left ; apply ih₁ a
        | SF_Iff_right a => apply SF_Iff_right; apply ih₂ a
      | False =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
      | Var name =>
        cases e₂_sf_e₁ with
        | SF_Self => assumption
  end Exercise₂

  section Exercise₃
    @[simp]
    def count_connectives (e: Expression): Nat :=
      match e with
      | .And  e₁ e₂ => 1 + count_connectives e₁ + count_connectives e₂
      | .Or   e₁ e₂ => 1 + count_connectives e₁ + count_connectives e₂
      | .Impl e₁ e₂ => 1 + count_connectives e₁ + count_connectives e₂
      | .Not  e     => 1 + count_connectives e
      | .Iff  e₁ e₂ => 1 + count_connectives e₁ + count_connectives e₂
      | .False      => 0
      | .Var _      => 0

    /- Alternatively, consider only unique subformulae (easy using List.unique). List.unique returns
       a list with at most the same nunber of elements as the list it is derived from, so the proof
       can be reused. -/
    @[simp]
    def get_all_subformulae (e: Expression) : List Expression :=
      match e with
      | .And  e₁' e₂' => e::(get_all_subformulae e₁' ++ get_all_subformulae e₂')
      | .Or   e₁' e₂' => e::(get_all_subformulae e₁' ++ get_all_subformulae e₂')
      | .Not  e'      => e::(get_all_subformulae e')
      | .Impl e₁' e₂' => e::(get_all_subformulae e₁' ++ get_all_subformulae e₂')
      | .Iff  e₁' e₂' => e::(get_all_subformulae e₁' ++ get_all_subformulae e₂')
      | _ => [e]

    def at_most_1_plus_two_times_connectives_count_subformulae:
      ∀e, (get_all_subformulae e).length ≤ 2*(count_connectives e) + 1
    := by
      intro e
      induction e with
      | False | Var _ => simp
      | _ => simp; ring_nf at *; lia
  end Exercise₃
end Subformulae

section TruthTables
  @[simp]
  def get_relevant_vars (e: Expression) : List String :=
    match e with
    | .And  e₁' e₂' => get_relevant_vars e₁' ++ get_relevant_vars e₂'
    | .Or   e₁' e₂' => get_relevant_vars e₁' ++ get_relevant_vars e₂'
    | .Not  e'      => get_relevant_vars e'
    | .Impl e₁' e₂' => get_relevant_vars e₁' ++ get_relevant_vars e₂'
    | .Iff  e₁' e₂' => get_relevant_vars e₁' ++ get_relevant_vars e₂'
    | .False => []
    | .Var name => [name]

  @[simp]
  def update_context (c: ContextT) (name: String) (value: Bool) :=
    Lean.AssocList.replace name value c

  @[simp]
  def is_tautology (e: Expression) : Prop :=
    ∀(c: ContextT) (c_ok: is_context_appropriate c e),
    eval_expr_prop e c c_ok

    /- TODO for situations w/ small number of variables: boolean interpretation + smthg for brute
       forcing -/
end TruthTables


lemma foo: ∀a b, (a ∧ b → b ∧ a) := by
  intro a b h
  obtain ⟨ah, bh⟩ := h
  constructor
  . assumption
  . assumption

lemma bar: ∀a b, (a ∨ b → b ∨ a) := by
  intro a b h
  obtain ah | bh := h
  . right; assumption
  . left; assumption
