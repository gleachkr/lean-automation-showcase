/- 
SLIDE 


Fun with lean automation
========================


FIN 
-/



/- 
SLIDE

Intro

Lean is a functional programming language.

Everything is an expression, there are no statements

FIN 
-/

/- SLIDE -/

/-

On the surface, it looks a bit like Haskell or OCaml.

You've got ADTs:

-/

inductive Workday  /- VS: "data Workdays = " -/
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday

/- SLIDE -/

/-

Pattern Matching:

(constructors are automatically namespaced by type, unlike Haskell)

-/

def feeling : Workday → String
| Workday.Monday => "ugh!"
| Workday.Friday => "yay!"
| _ => "😐"

/- FIN -/

/- SLIDE -/

/-

Standard higher order stuff, Polymorphism:

-/

#check List.map

#eval [1,2,3].map (λx => x + 1)

/-

Though, namespaces are used to provide a "method-like" syntax for some
function calls, so it looks a little like JavaScript 

-/

/- SLIDE -/

/- Recursive definitions are as you'd expect -/

def myPlus : Nat → Nat → Nat
| 0 , m => m
| .succ n, m => .succ (myPlus n m)

def myPlusAlt : Nat → Nat → Nat
| m , 0 => m
| n, .succ m => .succ (myPlusAlt n m)

/- SLIDE -/

/- 

And you've got monads, the haskell syntactic sugar for composing together terms
that have side-effects (broadly understood) when evaluated 

-/

def hello_world := do
  let x ← pure "hello"
  let y ← pure "world!"
  IO.print (x ++ " " ++ y)

#eval hello_world

/- SLIDE -/


/- Lean also has *dependent types* -/

inductive Vec : Nat → Type
| nil : Vec 0
| cons : Nat → Vec n → Vec (.succ n)

#check Vec.nil

#check Vec.cons 1 Vec.nil

def nvec : (n : Nat) → Vec n 
| 0 => Vec.nil
| n + 1 => Vec.cons 0 (nvec n)

/- And with dependent types, there's a crazy thing you can do -/

/- SLIDE -/

def kants_constant : myPlus 5 7 = myPlusAlt 5 7 := Eq.refl 12

/- SLIDE -/

/- in other words -/


theorem kants_theorem : myPlus 5 7 = myPlusAlt 5 7 := Eq.refl 12

/- SLIDE -/

/- More substantial theorems are possible. -/

theorem plus_equiv : (x y : Nat) → myPlus x y = myPlusAlt x y 
|     0,     0 => Eq.refl 0
| z + 1,     0 => by
  unfold myPlus
  rw [plus_equiv z 0]
  rfl
|     0, y + 1 => by 
  unfold myPlusAlt
  rw [←plus_equiv 0 y]
  rfl
| x + 1, y + 1 => by
  unfold myPlus myPlusAlt
  rw [plus_equiv x (y + 1), ←plus_equiv (x + 1) y] 
  unfold myPlus myPlusAlt
  rw [plus_equiv x y] 


theorem plus_equiv' : ∀(x y : Nat), myPlus x y = myPlusAlt x y := plus_equiv

/- SLIDE -/
