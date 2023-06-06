import
  tactic
  data.complex.basic
  algebra.euclidean_domain.basic

/--We will be considering quadratic integers of the form `x+y*α`, where `α=(1+√-7)/2`
and `x y : ℤ`.
We shall write `ℤα` for the Type of these integers, with a quadratic integer
integer represented by its x- and y-coordinates.
-/

@[ext]
structure ℤα : Type :=
  (x : ℤ)
  (y : ℤ)

namespace ℤα 
/--
We give lean a method for checking whether two Eisenstein integers are equal.
-/
instance dec_eq : decidable_eq ℤα := λ a b,
begin
  cases a with r s,
  cases b with t u,
  have : decidable (r=t ∧ s=u),
  {
    exact and.decidable,
  },
  apply decidable_of_decidable_of_iff this,
  tidy,
end

/--
We give lean a way of displaying elements of `ℤα` using the command `#eval`.
TO DO : rewrite this using pattern matching.
-/
def repr (a : ℤα) : string :=
begin
  by_cases a.x=0,
  {
    by_cases a.y=0,
    { exact "0" },
    { exact a.y.repr ++ " * α" }
  },
  {
    by_cases a.y=0,
    { exact a.x.repr },
    {
      by_cases a.y > 0,
      { exact a.x.repr ++ " + " ++ a.y.repr ++ " * α" },
      { exact a.x.repr ++ " - " ++ (-(a.y)).repr ++ " * α" }
    }
  }
end

instance ℤα_repr : has_repr ℤα :=
{ repr := repr }

#eval (⟨1, 2⟩:ℤα) 
#eval (⟨0,0⟩:ℤα)
#eval (⟨-4,0⟩:ℤα)
#eval (⟨0,-5⟩:ℤα)
#eval (⟨3,-5⟩:ℤα)

/-- Defining addition, multiplication and other things needed for rings-/

def zero : ℤα := ⟨0,0⟩
def one : ℤα := ⟨1,0⟩ 
def ω : ℤα := ⟨0,1⟩
def add : ℤα → ℤα → ℤα := λ a b, ⟨ a.x+b.x, a.y+b.y ⟩
def neg : ℤα → ℤα := λ a, ⟨ -a.x, -a.y ⟩

/--Using the fact that α^2 = α - 2, we obtain the rule for multiplication-/
def mul : ℤα → ℤα → ℤα := λ a b, ⟨ a.x*b.x - 2*a.y*b.y, a.x*b.y + a.y*b.x + a.y*b.y ⟩

end ℤα
