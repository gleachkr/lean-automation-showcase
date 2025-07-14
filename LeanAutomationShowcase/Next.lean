import LeanAutomationShowcase.First
import Duper
import Aesop
import Canonical
import Smt
import Smt.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
open Real

/- SLIDE

"It is unworthy of excellent people to lose hours like slaves in the labour of
calculation which could safely be relegated to anyone if machines were used." 

- Machina arithmetica in qua non additio tantum et subtractio sed et
  multiplicatio nullo, divisio vero paene nullo animi labore peragantur
  (Leibniz)

FIN -/

/- SLIDE -/

/-

Simp: extensible term rewriting guided by simp lemmas, uses proven equalities
and equivalences to try to prove a theorem by simplifying some of the expressions involved

-/

example (a b c : Nat) : (a + b) + c = a + (b + c) := by simp +arith

example : deriv (λx => cos (sin x)) x =  (sin ∘ sin) x * (- cos x) := by simp

example (a b : Nat) : (a = b + 1 ∨ b = a + 1) → (a > b ∨ b > a) := by
  simp +arith

/- SLIDE -/

/- omega, linarith, ring, bv_decide ... -/

example (x y : Real) : x^3 - y^3 = (x-y) * (x^2+x*y+y^2) := by ring

example : deriv (λx => cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by simp; ring

example : ∀(i  : UInt32),
  i = (i >>> 0x18 % 256) <<< 0x18 |||
      (i >>> 0x10 % 256) <<< 0x10 |||
      (i >>> 0x08 % 256) <<< 0x08 |||
      i % 256 := by bv_decide 
      /- This is surprisingly tedious to prove by hand! -/

/- SLIDE -/

/-

Aesop
=====

* proof search by tunable heuristics, working at the level of lean tactics
proofs. Generally performs proof construction steps that increase the amount
of available information without throwing things away, and ultimately attempts
to use simp to solve things.

-/

theorem know_by_cases' (a b : Nat) : (a = b + 1 ∨ b = a + 1) → (a > b ∨ b > a) := by aesop?

theorem know_by_cases'' (a b : Nat) : (a = b + 1 ∨ b = a + 1) → (a ≠ b) := by aesop?

/- It's limited when it comes to constructing new terms though -/

theorem something_bigger (a : Nat) : ∃b, b > a := by aesop

/- SLIDE -/

/- 

duper 

* backend is a superposition prover for higher-order logic, written in lean
  (negates conclusion, generates clauses looking for a contradiction)
  therefore classical

* Uses lean-auto to translate between higher-order logic and dependent type
  theory (can also do its own translations, but works best as a backend to
  lean-auto).

-/


theorem Grelling's_paradox : ∀Denotes: α → α → Prop, ¬∃y, ∀x, ¬Denotes x x ↔ Denotes y x := by duper

/- set_option trace.duper.printProof true in -/
theorem Prior's_paradox : ∀T : Prop → Prop, T (∀p, T p → ¬ p) → (∃p, T p ∧ ¬p) ∧ (∃p, T p ∧ p) := by duper

/- It's best at logical goals. Not so good at constructing witnesses. -/

theorem something_bigger' (a : Nat) : ∃b, b > a := by duper

/- SLIDE -/

/- canonical: constructs terms

* does a kind of guided breadth-first search (kind of like aesop), so that
  proof terms tend to be quite small (251× smaller on average in some testing)

* unlike Aesop, it works at the term level, not at the tactic level, so it
  can't itself involve tactics like simp.

* aspires to *completeness* for dependent type theory - it's in fact a rust
  program, in principle separable from lean.

quite good at finding witnesses

-/

theorem something_bigger'' (a : Nat) : ∃b, b > a := by canonical

/- SLIDE -/

/- 

A more interesting theorem: if a type α has more than one element, then no matter how
you map the type into α→α, there will always be some function you miss.

The proof involves constructing "the function you miss" given a map α→(α→α). 

Not entirely obvious how to do this!

(Given f:α→(α→α), you construct g: α→α that picks, for any a, something
different from `f a a`. Then g can't ever be `f a` for any a, because if it
were, we'd have `g a = f a a ≠ g a`.)

-/

example : DecidableEq α → (∃x y : α, x ≠ y) → ∀f : α → (α → α), ∃g : α → α, ¬∃x : α, f x = g := by
  intros dec neq₁ f
  have ⟨x,y,hyp⟩ := neq₁ 
  let g := λw => if f w w = x then y else x
  exists g
  rintro ⟨w, neq⟩
  have : f w w = g w := by duper [*]
  cases Classical.em (f w w = x)
  case inl h => 
    have leg₁ : g w = x := by canonical
    have leg₂ : g w = y := by canonical
    duper [*]
  case inr h => 
    have leg₁ : ¬g w = x := by canonical
    have leg₂ : g w = x := by canonical
    exact leg₁ leg₂

/- SLIDE -/

/- But canonical is not strictly better than duper. The examples below time out -/

/- example : ∀Denotes : α → α → Prop, ¬∃y, ∀x, Denotes x x ↔ ¬Denotes y y := 
  by canonical -/

/- example : ∀T : Prop → Prop, T (∀p, T p → ¬ p) → (∃p, T p ∧ ¬p) ∧ (∃p, T p ∧ p) := by canonical -/

/- SLIDE -/

/- 

Interestingly, canonical can also be used for program synthesis. Use an LSP
code action to replace the canonical invocation with the witnessing term it
found 

-/

def append : Vec n → Vec m → Vec (n + m) := by 
  canonical

#eval append (Vec.cons 5 Vec.nil) (Vec.cons 5 Vec.nil)

/- SLIDE -/

inductive PolyVec (α : Type) : Nat → Type
| nil : PolyVec α 0
| cons : α → PolyVec α n → PolyVec α (n + 1)

/- Program syntesis is most interesting when dealing with polymorphic types which -/
/- might have only one inhabitant, the one you'd naturally think of -/

def PolyAppend : PolyVec α n → PolyVec α m → PolyVec α (n + m) := by 
  canonical

/- SLIDE -/

/- Lean-SMT 

* translates lean goals into SMT solver queries, and translates SMT solver
outputs back into lean proofs. 

* currently supports theory of uninterpreted functions, and real number arithmetic.

-/

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  smt [h1]

example (ε δ : Real) (h : ε ≠ δ): ∃r : Real, (r < δ ∧ ε < r) ∨ (r < ε ∧ ε < r) := by smt [h]

example (ε δ : Real) (h : ε ≠ δ): ∃r : Real, (r < δ ∧ ε < r) ∨ (r < ε ∧ δ < r) := by 
  suffices  (∃r : Real, r < δ ∧ ε < r) ∨  (∃r : Real, r < ε ∧ δ < r) by duper [this]
  smt [h]


/- SLIDE

Making of 
=========

Getting all these tools running on one lean project is slightly painful.

You need to check compatible versions on https://reservoir.lean-lang.org/ and
then pin everything in your lakefile.

FIN -/

/- SLIDE
Worthy mentions: 

     https://reservoir.lean-lang.org/@JOSHCLUNE/Hammer - Intended as a common
     frontend to aesop, duper, and additional non-lean provers via lean-auto.

     https://reservoir.lean-lang.org/@verse-lab/veil - A verifier for
     automated and interactive proofs about transition systems. Uses SMT
     solvers and lean in concert to prove things about transition systems. Can
     verify protocols, distributive system behavior. Has a fancy DSL.

FIN -/
