import Lean.Data.AssocList
import Mathlib.Tactic.Ring

/- README BEFORE STARTING: this file supposes some degree of familiarity with Lean. It does *not*
   provide any information regarding the system: if you need that, please turn to online sources;
   see https://leanprover-community.github.io/learn.html for pointers.

   It defines a set of tactics that emulate the tree-based proof style we discussed in class inside
   of Lean. You are free to use them or to go your own way (though don't just delegate to automatic
   tactics, ofc).

   The exercises are located at the end of this file. -/


/- Reencoding the rules of natural deduction inside of Lean's  -/
/- Impl -/
lemma impl_elim {A B: Prop} : (A → B) → A → B := by lia
/- impl_intro: handled via the intro tactic -/

/- And -/
lemma and_intro      {A B: Prop} : A → B → A ∧ B := by lia
lemma and_elim_left  {A B: Prop} : A ∧ B → A     := by lia
lemma and_elim_right {A B: Prop} : A ∧ B → A     := by lia

/- Or -/
lemma or_intro_left  {A B: Prop} : A → A ∨ B := by lia
lemma or_intro_right {A B: Prop} : B → A ∨ B := by lia
lemma or_elim        {A B C: Prop} : A ∨ B → (A → C) → (B → C) → C := by lia

/- False -/
lemma dne {A : Prop} : ¬¬A → A := by lia
lemma raa {A : Prop} : (¬A → ⊥) → A := by intros h; by_cases A; lia; exfalso; apply h; lia
/- If you think about it hard enough, you can see that dne and raa really are the same (¬X is just
   syntactic sugar for X → ⊥) -/
lemma false_elim {A : Prop} : ⊥ → A := by intros f; simp at f

/- Bi-implication -/
lemma biimpl_intro      {A B: Prop} : (A → B) → (B → A) → (A ↔ B) := by lia
lemma biimpl_elim_left  {A B: Prop} : (A ↔ B) → A → B := by lia
lemma biimpl_elim_right {A B: Prop} : (A ↔ B) → B → A := by lia

/- Not -/
lemma not_intro {A: Prop} : (A → ⊥) → ¬A := by intros h; assumption
lemma not_elim  {A: Prop} : ¬A → A → ⊥   := by lia


/- Custom tactics (introduced through macros) -/
macro "impl_intro" name:ident: tactic => `(tactic| intros $name)
macro "impl_elim": tactic => `(tactic| apply impl_elim)
macro "and_intro": tactic => `(tactic| apply and_intro)
macro "and_elim_left": tactic => `(tactic| apply and_elim_left)
macro "and_elim_right": tactic => `(tactic| apply and_elim_right)
macro "or_elim": tactic => `(tactic| apply or_elim)
macro "or_intro_left": tactic => `(tactic| apply or_intro_left)
macro "or_intro_right": tactic => `(tactic| apply or_intro_right)
macro "dne": tactic => `(tactic| apply dne)
macro "raa": tactic => `(tactic| apply raa)
macro "false_elim": tactic => `(tactic| apply false_elim)
macro "biimpl_intro": tactic => `(tactic| apply biimpl_intro)
macro "biimpl_elim_left": tactic => `(tactic| apply biimpl_elim_left)
macro "biimpl_elim_right": tactic => `(tactic| apply biimpl_elim_right)
macro "not_intro": tactic => `(tactic| apply not_intro)
macro "not_elim": tactic => `(tactic| apply not_elim)

macro "from_premise" p:ident: tactic => `(tactic| apply $p)
macro "from_premise_auto": tactic => `(tactic| assumption)


/- Some examples -/
example {A B C: Prop} (P₁: A ∨ (B ∨ C)) (P₂: A → C) (P₃: B → C) : C := by
  or_elim /- Three branches: one per premise for this inference rule -/
  . /- Oh no, metavariables! This is what these variables of the form ?X are. They represent
       expressions whose exact value Lean could not deduce from the context alone. We can resolve
       the ambiguity by providing explicit values via the `change` tactic. -/
    change (A ∨ (B ∨ C)); from_premise P₁
  . impl_intro Pa
    . impl_elim
      . change A → C; from_premise P₂
      . from_premise_auto
  . impl_intro Pbvc
    . or_elim
      . change (B ∨ C); from_premise Pbvc
      . from_premise P₃
      . impl_intro Pc
        . from_premise Pc

example {A B: Prop} (a: A) (b: B) : (A ∧ B) ∧ (B ∧ A) := by
  and_intro
  . and_intro
    . from_premise a
    . from_premise b
  . and_intro
    . from_premise_auto /- Actually, there is no need to refer to the premises' name explicitly -/
    . from_premise_auto


/- Exercises (replace the sorries with actual proofs)
   Typing unicode symbols in Lean (refresher):
   . ∧: \and
   . ∨: \or
   . ⊥: \bot
   . →: \-> or \imp
   . ↔: \iff
   . ¬: \not
   . P₁: P\1

  I did not check every single tactic, any bugs left are yours to fix. -/
section Exercises
  variable (A B C: Prop)

  lemma exercise₁: A → (B → A) := by
    sorry

  lemma exercise₂: ⊥ → A := by
    sorry

  lemma exercise₃ (P: A → B) : A → (B ∨ C) := by
    sorry

  lemma exercise₄ (P: ¬C) (Q: (¬B) → C) : B := by
    sorry

  lemma exercise₅ (P: A) : ¬((¬A) ∧ B) := by
    sorry

  lemma exercise₆: (A → (¬A)) → (¬A) := by
    sorry

  lemma exercise₇: (A → B) ↔ ((¬B) → (¬A)) := by
    sorry
end Exercises
