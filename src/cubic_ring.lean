import
  tactic
  data.complex.basic
  algebra.euclidean_domain.basic
  algebra.group.defs
  algebra.group_power.ring
  algebra.group_power.basic
  data.real.irrational
  algebra.order.monoid.lemmas
  tactic.push_neg

open_locale classical

--set_option profiler true


--We will be considering cubic integers of the form `x+y*θ+z*(θ^2)`, where θ is the
--only real root of the cuic equation f(x) = x^3 + 3*(x^2) + 6*x + 2.
--and `x y z : ℤ`. We shall write `ℤθ` for the Type of these integers,
--and represent them by their f- , g- and h-coordinates.

@[ext]
structure ℤθ : Type :=
  (f : ℤ)
  (g : ℤ)
  (h : ℤ)

namespace ℤθ

--We give lean a method for checking whether two such integers are equal.

noncomputable
instance dec_eq : decidable_eq ℤθ  := infer_instance

-- NOTE : proof copied from quad ring, will need modification
-- λ a b,
-- begin
--   cases a with r s,
--   cases b with t u,
--   have : decidable (r=t ∧ s=u),
--   {
--     exact and.decidable,
--   },
--   apply decidable_of_decidable_of_iff this,
--   tidy,
-- end

--We give lean a way of displaying elements of `ℤθ` using the command `#eval`.
--TO DO : rewrite this using pattern matching.

def repr (a : ℤθ) : string :=
begin
 by_cases a.f=0,
 {
  by_cases a.g=0,
  {
   by_cases a.h=0,
   { exact "0" },
   { exact a.h.repr ++ " * θ^2"},
  },
  {
   by_cases a.h=0,
   { exact a.g.repr ++ " * θ"},
   { 
    by_cases a.h > 0,
    {exact a.g.repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"},
    {exact a.g.repr ++ " * θ" ++ " - " ++ (-(a.h)).repr ++ " * θ^2"},
   },
  },
 },
 {
  by_cases a.g=0,
  {
   by_cases a.h=0,
   {exact a.f.repr},
   { 
    by_cases a.h > 0,
    {exact a.f.repr ++ " + " ++ a.h.repr ++ " * θ^2"},
    {exact a.f.repr ++ " - " ++ (-(a.h)).repr ++ " * θ^2"},
   },
  },
  {
    by_cases a.h=0,
    {
     by_cases a.g > 0,
     {exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ"},
     {exact a.f.repr ++ " - " ++ (-(a.g)).repr ++ " * θ"}
    },
    {
     by_cases a.g > 0,
     {
      by_cases a.h > 0,
      {exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"},
      {exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ" ++ " - " ++ (-(a.h)).repr ++ " * θ^2"},
     },
     {
      by_cases a.h > 0,
      {exact a.f.repr ++ " - " ++ (-(a.g)).repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"},
      {exact a.f.repr ++ " - " ++ (-(a.g)).repr ++ " * θ" ++ " - " ++ (-(a.h)).repr ++ " * θ^2"},
     },
    },
  },
 },
 end



instance ℤθ_repr : has_repr ℤθ :=
{ repr := repr }

#eval (⟨ 0,-9,-1⟩ : ℤθ)

/-- Defining addition, multiplication and other things needed for rings-/

def zero : ℤθ := ⟨0,0, 0⟩
def one : ℤθ := ⟨1,0, 0⟩
def θ : ℤθ := ⟨0,1, 0⟩
def θ_sq : ℤθ := ⟨0, 0, 1⟩
def add : ℤθ → ℤθ → ℤθ := λ a b, ⟨ a.f+b.f, a.g+b.g, a.h+b.h ⟩
def neg : ℤθ → ℤθ := λ a, ⟨ -a.f, -a.g, -a.h ⟩

/--Using the fact that θ^3 + 3*(θ^2) + 6*θ + 2 = 0, we obtain the rule for multiplication-/

def mul : ℤθ → ℤθ → ℤθ := λ a b, ⟨ a.f*b.f + 6*a.h*b.h - 2*a.g*b.h - 2*a.h*b.g, a.f*b.g + a.g*b.f + 16*a.h*b.h - 6*a.g*b.h - 6*a.h*b.g, a.f*b.h + a.h*b.f + a.g*b.g + 3*a.h*b.h - 3*a.g*b.h - 3*a.h*b.g⟩ 

variables a b c : ℤθ 

lemma my_add_assoc : add (add a b) c = add a (add b c) :=
begin
  cases a, cases b, cases c,
  simp only [add,add_assoc],
  tautology,
end

lemma my_zero_add : add zero a = a :=
begin
  cases a with x y,
  simp only [add,zero,zero_add],
  tautology,
end

lemma my_add_zero : add a zero = a :=
begin
  cases a with x y,
  simp only [add,zero,add_zero],
  tautology,
end

lemma my_add_left_neg : add (neg a) a = zero :=
begin
  cases a,
  simp only [neg,add],
  --NOTE TO SELF: these two lines cannot be merged. Why not ????
  simp only [add_left_neg],
  tautology,
end

lemma my_add_comm : add a b = add b a :=
begin
  cases a, cases b,
  simp only [add,add_comm],
  tautology,
end

lemma my_mul_assoc : mul (mul a b) c = mul a (mul b c) :=
begin
  cases a, cases b, cases c,
  simp only [mul],
  split,
  ring,
  split,
  ring,ring,
end

lemma my_one_mul : mul one a = a :=
begin
  cases a,
  simp [mul,one],
end

lemma my_mul_one : mul a one = a :=
begin
  cases a,
  simp [mul,one],
end

lemma my_left_distrib : mul a (add b c) = add (mul a b) (mul a c) :=
begin
  cases a, cases b, cases c,
  simp only [mul,add],
  split,
  ring,
  split,
  ring, ring,
end

lemma my_right_distrib : mul (add a b) c = add (mul a c) (mul b c) :=
begin
  cases a, cases b, cases c,
  simp only [mul,add],
  split,
  ring,
  split,
  ring, ring,
end

lemma my_mul_comm : mul a b = mul b a :=
begin
  cases a, cases b,
  simp only [mul],
  split,
  ring,
  split,
  ring, ring,
end

def zsmul : ℤ → ℤθ → ℤθ := λ n a, ⟨n*a.f, n*a.g, n*a.h⟩

lemma my_zsmul_zero' : ∀ (a : ℤθ), zsmul (0:ℤ)  a = (zero) :=
begin
intro a,
unfold zsmul,
rw zero_mul,
rw zero_mul,
rw zero_mul,
rw ← zero,
end

lemma my_zsmul_succ' : ∀ (n : ℕ) (a : ℤθ), zsmul (int.of_nat n.succ) a = a.add (zsmul (int.of_nat n) a) :=
begin
intros n a,
change (⟨int.of_nat n.succ*a.f, int.of_nat n.succ*a.g, int.of_nat n.succ*a.h⟩:ℤθ) = (⟨a.f + int.of_nat n*a.f, a.g + int.of_nat n*a.g, a.h + int.of_nat n*a.h⟩:ℤθ),
norm_num,
split,
linarith,
split,
linarith, linarith,
end

lemma my_zsmul_neg' : ∀ (n : ℕ) (a : ℤθ), zsmul -[1+ n] a = (zsmul ↑(n.succ) a).neg :=
begin
intros n a,
simp,
change (⟨int.neg_succ_of_nat n*a.f, int.neg_succ_of_nat n*a.g, int.neg_succ_of_nat n*a.h⟩:ℤθ) = (⟨-(int.of_nat n.succ*a.f), -(int.of_nat n.succ*a.g), -(int.of_nat n.succ*a.h)⟩:ℤθ),
simp,
split,
rw int.neg_succ_of_nat_coe,
rw int.neg_mul_eq_neg_mul_symm,
rw int.coe_nat_add,
rwa int.coe_nat_one,
split,
rw int.neg_succ_of_nat_coe,
rw int.neg_mul_eq_neg_mul_symm,
rw int.coe_nat_add,
rwa int.coe_nat_one,
rw int.neg_succ_of_nat_coe,
rw int.neg_mul_eq_neg_mul_symm,
rw int.coe_nat_add,
rwa int.coe_nat_one,
end

def int_cast : ℤ → ℤθ := λ a, ⟨a, 0, 0⟩ 
def nat_cast : ℕ → ℤθ := λ a, ⟨a, 0, 0⟩

lemma my_nat_cast_zero : nat_cast 0 = zero :=
begin
unfold nat_cast,
rw int.coe_nat_zero,
refl,
end

lemma my_nat_cast_succ : ∀ (n : ℕ), nat_cast (n + 1) = (nat_cast n).add one :=
begin
intro n,
change (⟨int.of_nat (n+1), 0, 0⟩:ℤθ) = (⟨int.of_nat n + 1, 0, 0⟩:ℤθ),
simp,
end

lemma my_int_cast_of_nat : ∀ (n : ℕ), int_cast ↑n = nat_cast n :=
begin
intro n,
refl,
end

lemma my_int_cast_neg_succ_of_nat : ∀ (n : ℕ), int_cast (-↑(n + 1)) = (nat_cast (n + 1)).neg :=
begin
intro n,
refl,
end

/-- Making ℤθ into a ring-/

instance is_ring : comm_ring ℤθ :=
{
  zero := zero,
  neg := neg,
  add := add,
  one := one,
  mul := mul,
  add_assoc := my_add_assoc,
  zero_add := my_zero_add,
  add_zero := my_add_zero,
  add_left_neg := my_add_left_neg,
  add_comm := my_add_comm,
  mul_assoc := my_mul_assoc,
  one_mul := my_one_mul,
  mul_one := my_mul_one,
  left_distrib := my_left_distrib,
  right_distrib := my_right_distrib,
  mul_comm := my_mul_comm,

  zsmul := zsmul,
  zsmul_zero' := my_zsmul_zero',
  zsmul_succ' := my_zsmul_succ',
  zsmul_neg' := my_zsmul_neg',

  int_cast := int_cast,
  nat_cast := nat_cast,

  nat_cast_zero := my_nat_cast_zero,
  nat_cast_succ := my_nat_cast_succ,
  int_cast_of_nat := my_int_cast_of_nat,
  int_cast_neg_succ_of_nat := my_int_cast_neg_succ_of_nat,
}

#eval θ^3
#eval θ^4
#eval (25+13*θ+5*θ^2)^3
#eval (-1-3*θ-θ^2)^2

def Norm : ℤθ → ℤ := λ k, | k.f^3 - 2*k.g^3 + 4*k.h^3 - 3*k.f^2*k.g - 3*k.f^2*k.h + 6*k.f*k.g^2 + 6*k.g^2*k.h + 24*k.f*k.h^2 - 12*k.g*k.h^2 - 12*k.f*k.g*k.h |

def unit : (ℤθ)ˣ := ⟨ -1 - 3*θ - θ^2 , 25 + 13 * θ + 5 * θ^2, by ext; dec_trivial, by ext; dec_trivial ⟩

lemma unit_l : (unit:ℤθ) = ⟨-1, -3, -1⟩ :=
begin
refl,
end

lemma unit_neg_1 : (((unit ^ -(1:ℤ)):ℤθˣ):ℤθ) = ⟨25, 13, 5⟩:=
begin
refl,
end

lemma simp_norm (a b : ℤ) : Norm (⟨a, -b, 0⟩:ℤθ) = |a^3 + 3*a^2*b + 6*a*b^2 + 2*b^3| :=
begin
unfold Norm,
dsimp,
ring_nf,
end

lemma mul_mule_3 (a b : ℤθ) : a*b = (⟨ a.f*b.f + 6*a.h*b.h - 2*a.g*b.h - 2*a.h*b.g, a.f*b.g + a.g*b.f + 16*a.h*b.h - 6*a.g*b.h - 6*a.h*b.g, a.f*b.h + a.h*b.f + a.g*b.g + 3*a.h*b.h - 3*a.g*b.h - 3*a.h*b.g⟩:ℤθ) :=
begin   
refl,
end

lemma norm_mul (r s : ℤθ) : Norm r * Norm s = Norm (r*s) :=
begin
-- unfold Norm,
-- rw mul_mule_3 r s,
-- dsimp,
-- rw ← abs_mul,
-- ring_nf,
sorry,
end

lemma Norm_divides {p a : ℤθ} (h : p ∣ a) : (Norm p ∣ Norm a):=
begin
cases h with n hn,
use Norm n,
rw norm_mul p n,
rw hn,
end

lemma norm_one_if_unit (k : ℤθ) : is_unit k → Norm k = 1 :=
begin
intro h,
rw is_unit_iff_exists_inv at h,
have p : ∃ (b : ℤθ), 1 = k * b := by tauto,
change k ∣ 1 at p,
have l := Norm_divides p,
have d : Norm 1 = 1 := by ring,
rw d at l,
refine int.eq_one_of_dvd_one _ l,
exact abs_nonneg _,
end

--this is to be left for later. This is the hardest part of the proof.
lemma units_are  (a : (ℤθ)ˣ) : ∃n : ℤ ,
  a = unit^n ∨ a = - unit^n :=
  begin
  sorry,
  end

--The usual maths definition for y % 3 = s
lemma y_mod_three (y:ℤ) (s:ℤ) (h : y % 3 = s) : ∃(k:ℤ), y = 3*k + s :=
begin
have q := int.dvd_sub_of_mod_eq h,
cases q with l lh,
use l,
exact eq_add_of_sub_eq lh,
end 

lemma unit_sq : (((unit ^ 2):ℤθˣ):ℤθ) = ⟨-5, -14, -4⟩ :=
begin
rw pow_two,
have h : (((unit * unit):ℤθˣ):ℤθ) = ((unit:ℤθˣ):ℤθ) * ((unit:ℤθˣ):ℤθ),
 {
  refl,
 },
rw h,
rw unit_l,
rw mul_mule_3, dsimp, norm_num,
end

lemma unit_cubed : (unit:ℤθ)^3 = ⟨-23, -63, -15⟩ :=
begin
rw pow_three,
nth_rewrite 1 unit_l, nth_rewrite 1 unit_l,
nth_rewrite 1 mul_mule_3,
dsimp, ring_nf,
end

lemma unit_inv_cubed : (((unit ^ (-3:ℤ)):ℤθˣ):ℤθ) = ⟨10591, 5553, 2139⟩ :=
begin
rw ← mul_neg_one,
rw mul_comm, rw zpow_mul, 
have q : (3:ℤ) = 2 + 1 := by dec_trivial,
nth_rewrite 0 q, rw zpow_add, rw zpow_one, rw zpow_two,
rw mul_assoc,
--how did that work?
change (((unit ^ (-1:ℤ)):ℤθˣ):ℤθ) * ((((unit ^ (-1:ℤ)):ℤθˣ) * ((unit ^ (-1:ℤ)):ℤθˣ)):ℤθ) = ⟨10591, 5553, 2139⟩,
rw unit_neg_1,
nth_rewrite 1 mul_mule_3,
dsimp, norm_num,
rw mul_mule_3,
dsimp, norm_num,
end

lemma unit_pow_zero : ((((unit^(3*0)):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*0)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*0)):ℤθˣ):ℤθ)).h % 3 = 0 :=
begin
split,
refl,
split,
refl, refl,
end

lemma unit_pow_one : ((((unit^(1)):ℤθˣ):ℤθ)).f % 3 = 2 ∧ ((((unit^(1)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(1)):ℤθˣ):ℤθ)).h % 3 = 2 :=
begin
split,
refl,
split,
refl, refl,
end

lemma unit_pow_zero_mod_three : ∀(k:ℕ), (((((unit^(3*(k:ℤ))):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*(k:ℤ))):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*(k:ℤ))):ℤθˣ):ℤθ)).h % 3 = 0) ∧ (((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).h % 3 = 0) :=
begin
intro k,
split,
{
  induction k with b hb,
   {
    exact unit_pow_zero,
   },
  cases hb with h1 h23,
  cases h23 with h2 h3,
  have p : b.succ = b + 1 := by refl,
  repeat {rw p},
  have w : ((unit ^ (3 * (b + 1))):ℤθ) = ((unit ^ (3 * b)):ℤθ) * ((unit ^ (3)):ℤθ),
   {
    rw [mul_add, mul_one, pow_add],
   },
  have t1 : ((unit:ℤθ)^(3 * b)).f % 3 = 1,
   {
    norm_cast,
    exact h1,
   },
  have t2 : ((unit:ℤθ)^(3 * b)).g % 3 = 0,
   {
    norm_cast,
    exact h2,
   },
  have t3 : ((unit:ℤθ)^(3 * b)).h % 3 = 0,
   {
    norm_cast,
    exact h3,
   },
  have r1 := y_mod_three ((unit ^ (3 * b)):ℤθ).f 1 t1,
  cases r1 with c1 hc1,
  have r2 := y_mod_three ((unit ^ (3 * b)):ℤθ).g 0 t2,
  cases r2 with c2 hc2,
  rw add_zero at hc2,
  have r3 := y_mod_three ((unit ^ (3 * b)):ℤθ).h 0 t3,
  cases r3 with c3 hc3,
  rw add_zero at hc3,
  have s : ((unit ^ (3 * b)):ℤθ) = ⟨ 3*c1 + 1, 3*c2, 3*c3⟩,
   {
    ext; dsimp,
    exact hc1, exact hc2, exact hc3,
   },
  -- just the same as w?
  have s1 : ((unit ^ (3 * (b + 1))):ℤθ) = ((unit ^ (3 * b)):ℤθ) * ((unit ^ 3):ℤθ),
   {
    rw ← pow_add,
    rw [mul_add, mul_one],
   },
  rw s at s1, rw unit_cubed at s1,
  rw mul_mule_3 at s1, dsimp at s1, ring_nf at s1,
  rw ext_iff at s1, dsimp at s1, 
  norm_cast at s1,
  cases s1 with f1 f23,
  cases f23 with f2 f3,
  norm_cast,
  rw mul_add, rw mul_one,
  rw [f1, f2, f3],
  split,
   {
    rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
    norm_num,
    rw int.add_mod, rw int.mul_mod,
    norm_num,
    rw int.sub_mod, rw int.mul_mod,
    norm_num,
   },
  split,
   {
    norm_num,
    use (-(63*c1) + (138 * c3 + (67 * c2 - 21))),
    ring_nf,
   },
   {
    norm_num,
    use (-(15*c1) + (121 * c3 + (-(18 * c2) - 5))),
    ring_nf,
   },
},
{
  induction k with b hb,
   {
    rw [int.coe_nat_zero, neg_zero, mul_zero],
    exact unit_pow_zero,
   },
  cases hb with h1 h23,
  cases h23 with h2 h3,
  have p : b.succ = b + 1 := by refl,
  rw p, -- why is it auto repeating?
  --why this notation?
  have w : (((unit ^ ((3:ℤ) * -((b + 1):ℤ))):ℤθˣ):ℤθ) = (((unit ^ (3 * -(b:ℤ))):ℤθˣ):ℤθ) * (((unit ^ (-3:ℤ)):ℤθˣ):ℤθ),
   {
    rw [neg_add, mul_add, mul_neg_one, zpow_add],
    norm_cast,
   },
  have r1 := y_mod_three (((unit ^ ((3:ℤ) * -((b):ℤ))):ℤθˣ):ℤθ).f 1 h1,
  cases r1 with c1 hc1,
  have r2 := y_mod_three (((unit ^ ((3:ℤ) * -((b):ℤ))):ℤθˣ):ℤθ).g 0 h2,
  cases r2 with c2 hc2,
  rw add_zero at hc2,
  have r3 := y_mod_three (((unit ^ ((3:ℤ) * -((b):ℤ))):ℤθˣ):ℤθ).h 0 h3,
  cases r3 with c3 hc3,
  rw add_zero at hc3,
  have s : (((unit ^ ((3:ℤ) * -((b):ℤ))):ℤθˣ):ℤθ) = ⟨ 3*c1 + 1, 3*c2, 3*c3⟩,
   {
    ext; dsimp,
    exact hc1, exact hc2, exact hc3,
   },
  rw s at w, rw unit_inv_cubed at w,
  rw mul_mule_3 at w, dsimp at w, ring_nf at w,
  rw ext_iff at w, dsimp at w,
  cases w with w1 w23,
  cases w23 with w2 w3,
  have j : (-(3 * (b:ℤ)) - 3) = 3 * -((b + 1):ℤ),
   {
    rw mul_comm,
    rw ← neg_mul,
    rw mul_comm,
    rw sub_eq_add_neg,
    nth_rewrite 1 ← mul_neg_one,
    rw ← mul_add,
    rw ← neg_add,
   },
  have j1 : (b:ℤ) + 1 = ((((b + 1):ℕ)):ℤ),
   {
    norm_cast,
   },
  rw j1 at j,
  rw j at w1, rw j at w2, rw j at w3,
  rw [w1, w2, w3],
  clear h1 h2 h3 p hc1 hc2 hc3 w1 w2 w3 s j j1,
  split,
   {
    rw int.add_mod, rw int.mul_mod, norm_num,
    rw int.add_mod, rw int.mul_mod, norm_num,
    rw int.add_mod, rw ← neg_mul, rw int.mul_mod, norm_num,
   },
  split,
   {
    norm_num,
    use (5553*c1 + (906 * c3 + (-(2243 * c2) + 1851))),
    ring_nf,
   },
   {
    norm_num,
    use (2139 * c1 + (349 * c3 + (-(864 * c2) + 713))),
    ring_nf,
   },
},
end

lemma unit_zpow_zero_mod_three : ∀(k:ℤ), (((((unit^(3*k)):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*k)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*k)):ℤθˣ):ℤθ)).h % 3 = 0) :=
begin
intro q,
have h := lt_or_le 0 q,
have p := unit_pow_zero_mod_three,
cases h with h1 h2,
 {
  specialize p (int.to_nat q),
  cases p with p1 p2,
  rw int.to_nat_of_nonneg (le_of_lt h1) at p1,
  exact p1,
 },
 specialize p (int.to_nat (-q)),
 cases p with p1 p2,
 have r := neg_le_neg h2,
 rw neg_zero at r,
 rw int.to_nat_of_nonneg r at p2,
 rw neg_neg at p2,
 exact p2,
end

lemma unit_zpow_one_mod_three : ∀(k:ℤ), (((((unit^(3*k + 1)):ℤθˣ):ℤθ)).f % 3 = 2 ∧ ((((unit^(3*k + 1)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*k + 1)):ℤθˣ):ℤθ)).h % 3 = 2) :=
begin
intro k,
have w : ((((unit^(3*k + 1)):ℤθˣ):ℤθ)) = (((unit^(3*k)):ℤθˣ):ℤθ) * (((unit^(1)):ℤθˣ):ℤθ),
 {
  rw zpow_add,
  norm_cast,
 },
have g := unit_zpow_zero_mod_three,
specialize g k,
cases g with g1 g23,
cases g23 with g2 g3,
have t1 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).f 1 g1,
cases t1 with j1 hj1,
have t2 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).g 0 g2,
cases t2 with j2 hj2,
rw add_zero at hj2,
have t3 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).h 0 g3,
cases t3 with j3 hj3,
rw add_zero at hj3,
have s : (((unit ^ (3*k)):ℤθˣ):ℤθ) = ⟨ 3*j1 + 1, 3*j2, 3*j3⟩,
 {
   ext; dsimp,
   exact hj1, exact hj2, exact hj3,
 },
clear g1 g2 g3 hj1 hj2 hj3,
rw s at w, rw pow_one at w, rw unit_l at w,
rw mul_mule_3 at w, dsimp at w, ring_nf at w,
rw ext_iff at w,
dsimp at w,
cases w with w1 w23,
cases w23 with w2 w3,
rw [w1, w2, w3],
split,
 {
  rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
  norm_num,
  rw int.sub_mod, rw int.mul_mod,
  norm_num,
 },
split,
 {
  rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
  norm_num,
  use (2*j3 + (5*j2 -1)),
  ring_nf,
 },

rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
norm_num,
rw int.sub_mod, rw int.mul_mod,
norm_num,
end

lemma unit_zpow_two_mod_three : ∀(k:ℤ), (((((unit^(3*k + 2)):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*k + 2)):ℤθˣ):ℤθ)).g % 3 = 1 ∧ ((((unit^(3*k + 2)):ℤθˣ):ℤθ)).h % 3 = 2) :=
begin
intro k,
have w : ((((unit^(3*k + 2)):ℤθˣ):ℤθ)) = (((unit^(3*k)):ℤθˣ):ℤθ) * (((unit^(2)):ℤθˣ):ℤθ),
 {
  rw zpow_add,
  norm_cast,
 },
have g := unit_zpow_zero_mod_three,
specialize g k,
cases g with g1 g23,
cases g23 with g2 g3,
have t1 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).f 1 g1,
cases t1 with j1 hj1,
have t2 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).g 0 g2,
cases t2 with j2 hj2,
rw add_zero at hj2,
have t3 := y_mod_three (((unit ^ (3*k)):ℤθˣ):ℤθ).h 0 g3,
cases t3 with j3 hj3,
rw add_zero at hj3,
have s : (((unit ^ (3*k)):ℤθˣ):ℤθ) = ⟨ 3*j1 + 1, 3*j2, 3*j3⟩,
 {
   ext; dsimp,
   exact hj1, exact hj2, exact hj3,
 },
clear g1 g2 g3 hj1 hj2 hj3,
rw s at w, rw unit_sq at w,
rw mul_mule_3 at w, dsimp at w, ring_nf at w,
rw ext_iff at w,
dsimp at w,
cases w with w1 w23,
cases w23 with w2 w3,
rw [w1, w2, w3],
split,
 {
  rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
  norm_num,
  rw int.add_mod, rw int.mul_mod,
  norm_num,
  rw int.sub_mod, rw int.mul_mod,
  norm_num,
 },
split,
 {
  rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
  norm_num,
  rw int.add_mod, rw int.mul_mod,
  norm_num,
  rw int.sub_mod, rw int.mul_mod,
  norm_num,
 },

rw int.add_mod, rw ← neg_mul, rw int.mul_mod,
norm_num,
rw int.add_mod, rw int.mul_mod,
norm_num,
rw int.sub_mod, rw ← neg_mul, rw int.mul_mod,
norm_num,
end

--the below should definitely be simplified!
lemma mul_three_pow_dvd (n : ℕ) (j : 1 ≤ n) : ∃ (a:ℕ), (3^a ∣ 3*n) ∧ (¬(3^(a + 1) ∣ 3*n)) :=
begin
by_contra,
rw push_neg.not_exists_eq at h,
have r : ∀ (x : ℕ), ¬(3 ^ x ∣ 3 * n) ∨  (3 ^ (x + 1) ∣ 3 * n),
 {
  intro g,
  specialize h g,
  rw push_neg.not_and_distrib_eq at h,
  rw push_neg.not_not_eq at h,
  exact h,
 },
clear h,
have s : ∀ (x : ℕ), (¬(3 ^ x ∣ 3 * n) ∧ ¬(3 ^ (x + 1) ∣ 3 * n)) ∨ ((3 ^ x ∣ 3 * n) ∧ (3 ^ (x + 1) ∣ 3 * n)),
 {
  intro g,
  specialize r g,
  cases r with r1 r2,
   {
    left,
    split, exact r1,
    by_contra,
    change ∃ (l : ℕ), 3*n = (3^(g + 1)) * l at h,
    cases h with k hk,
    rw [pow_add, pow_one, mul_assoc] at hk,
    have f : 3^g ∣ 3*n,
     {
      use (3 *k),
      exact hk,
     },
    have s : (3^g ∣ 3*n) ∧ ¬(3^g ∣ 3*n),
     {
      split, exact f, exact r1,
     },
    simp at s, exact s,
   },
   right,
   split,
   change ∃ (l : ℕ), 3*n = (3^(g + 1)) * l at r2,
   cases r2 with k hk,
   rw [pow_add, pow_one, mul_assoc] at hk,
   use (3*k),
   exact hk, exact r2,
 },
clear r,
have t : ∀ (f : ℕ), (3^f ∣ 3*n),
 {
  intro g,
  induction g with k hk,
  norm_num,
  specialize s k,
  cases s with s1 s2,
   {
    exfalso,
    cases s1 with s3 s4,
    have t : (3^k ∣ 3*n) ∧ ¬(3^k ∣ 3 * n),
     {
      split, exact hk, exact s3,
     },
    simp at t, exact t,
   },
   cases s2 with s5 s6,
   exact s6,
 },
 specialize t (n + 1),
have q : ∀ (f : ℕ), (3^(f + 1)) > 3*f,
 {
  intro g,
  induction g with k hk,
  norm_num,
  change 3^(k + 1 + 1) > 3*(k+1),
  have ss : k = 0 ∨ 0 < k := nat.eq_zero_or_pos k,
  cases ss, rw ss, norm_num,
  rw pow_add, rw pow_one, rw mul_comm, 
  simp,
  change 1 ≤ k at ss,
  have b : k < 2*k,
   {
    change 0 < k at ss,
    exact lt_two_mul_self ss,
   },
  have q1 : k + 1 < 3*k,
   {
    have finally := add_lt_add_of_lt_of_le b ss,
    nth_rewrite 2 ← one_mul k at finally,
    rw ← right_distrib at finally,
    norm_num at finally,
    exact finally,
   },
  have q2 := lt_trans q1 hk,
  exact q2,
 },

specialize q n,
have r : ¬(3 ^ (n + 1) ∣ 3 * n),
 {
  clear t, by_contra,
  change ∃ (l : ℕ), 3*n = 3^(n + 1) * l at h,
  cases h with p hp,
  rw hp at q,
  have ss : p = 0 ∨ 0 < p := nat.eq_zero_or_pos p,
  cases ss,
  rw ss at hp, norm_num at hp, rw hp at j, norm_num at j,
  simp at q, rw q at ss, norm_num at ss,
 },
have w: (3 ^ (n + 1) ∣ 3 * n) ∧ ¬(3 ^ (n + 1) ∣ 3 * n),
 {
  split, exact t, exact r,
 },
simp at w, exact w,
end

lemma rep_mod_three (n : ℕ) : ∃ (a : ℕ), (n = 3*a) ∨ (n = 3*a + 1) ∨ (n = 3*a + 2) :=
begin
induction n with k hk,
use 0, left, rw mul_zero,
cases hk with j hj, cases hj with h1 h23,
use j, right, left, 
change k + 1 = 3*j + 1, rw add_left_inj 1, exact h1,
cases h23 with h2 h3,
use j, right, right,
change k + 1 = 3*j + 2, 
rw ← one_add_one_eq_two, rw ← add_assoc,
rw add_left_inj 1, exact h2,
use (j + 1), left,
change k + 1 = 3*(j + 1),
rw mul_add, rw mul_one,
have babymath : 3 = 2 + 1 := by norm_num,
nth_rewrite 1 babymath, rw ← add_assoc,
rw add_left_inj 1, exact h3,
end

lemma mul_three_expansion (n : ℕ) (h : 1 ≤ n) : ∃ (a:ℕ) (b:ℤ), (1 ≤ a) ∧ (3*(n:ℤ) = 3^a * (3*b+1) ∨ 3*(n:ℤ) = 3^a * (3*b+2)) :=
begin
have q := mul_three_pow_dvd n h,
cases q with k hk, cases hk with h1 h2,
have ss : k = 0 ∨ 0 < k := nat.eq_zero_or_pos k,
cases ss with s1 s2,
rw [s1, zero_add, pow_one] at h2, exfalso, 
have p : 3 ∣ 3*n,
 {
  use n,
 },
have contra : (3 ∣ 3*n) ∧ ¬(3 ∣ 3*n),
 {
  split, exact p, exact h2,
 },
simp at contra, exact contra,
change 1 ≤ k at s2,
change ∃ (l : ℕ), 3*n = (3^k) * l at h1, cases h1 with j hj,
have p := rep_mod_three j, cases p with r hr,
cases hr with t1 t23,
 {
  exfalso,
  rw t1 at hj, rw ← mul_assoc at hj,
  nth_rewrite 2 ← pow_one 3 at hj, rw ← pow_add at hj,
  have g : 3^(k + 1) ∣ 3*n,
   {
    use r, exact hj,
   },
  have combine : (3^(k+1) ∣ 3*n) ∧ ¬(3^(k+1) ∣ 3*n),
   {
    split, exact g, exact h2,
   },
  simp at combine, exact combine,
 },
cases t23 with t2 t3,
 {
  rw t2 at hj,
  use k, use r,
  split, exact s2,
  left, exact_mod_cast hj,
 },

rw t3 at hj,
use k, use r,
split, exact s2,
right, exact_mod_cast hj,
end

lemma zmul_three_expansion (n : ℤ) (h : n ≠ 0) : ∃ (a:ℕ) (b:ℤ), ((1 ≤ a) ∧ (3*n = 3^a * (3*b+1) ∨ 3*n = 3^a * (3*b+2))) :=
begin
have p : n ≥ 0 ∨ n < 0,
 {
  have w := lt_or_le 0 n,
  cases w with w1 w2,
  left, rw ge_iff_le, rw le_iff_lt_or_eq, left, exact w1,
  rw le_iff_lt_or_eq at w2,
  cases w2 with w3 w4,
  right, exact w3,
  left, rw ge_iff_le, rw le_iff_lt_or_eq, right, exact eq.symm w4,
 },
cases p with p1 p2,
rw ge_iff_le at p1, rw le_iff_eq_or_lt at p1,
cases p1 with p3 p4,
have t : (n = 0) ∧ (n ≠ 0),
 {
  split, exact eq.symm p3, exact h,
 },
exfalso,
simp at t, exact t,
have p5 : 1 ≤ (int.to_nat n),
 {
  have s := nat.eq_zero_or_pos (int.to_nat n),
  cases s with s1 s2,
  exfalso,
  simp at s1,
  rw ← push_neg.not_lt_eq at s1,
  have please : (0 < n) ∧ ¬(0 < n),
   {
    split, exact p4, exact s1,
   },
  change (0 < n) ∧ ¬(0 < n) at please, 
  --OMG why?
  {
   apply s1, exact p4,
  },
 change 1 ≤ (int.to_nat n) at s2, exact s2,
 },
 
have r1 := mul_three_expansion (int.to_nat n) p5,
cases r1 with j hj, cases hj with g hg, cases hg with hg0 hg12, 
use j, use g,
split, exact hg0,
have coe_coe : ((int.to_nat n):ℤ) = n,
 {
  have finale := le_of_lt p4,
  exact int.to_nat_of_nonneg finale,
 },
cases hg12 with hg1 hg2,
rw coe_coe at hg1, left, exact hg1,
rw coe_coe at hg2, right, exact hg2,

have p6 : 1 ≤ (int.to_nat (-n)),
 {
  have s := nat.eq_zero_or_pos (int.to_nat (-n)),
  cases s with s1 s2,
  exfalso,
  simp at s1,
  rw ← push_neg.not_lt_eq at s1,
  have please : (n < 0) ∧ ¬(n < 0),
   {
    split, exact p2, exact s1,
   },
  change (n < 0) ∧ ¬(n < 0) at please, 
  --OMG why?
  {
   apply s1, exact p2,
  },
 change 1 ≤ (int.to_nat (-n)) at s2, exact s2,
 },
 
have r2 := mul_three_expansion (int.to_nat (-n)) p6,
cases r2 with j hj, cases hj with g hg, cases hg with hg0 hg12, 
have coe_coe : -((int.to_nat (-n)):ℤ) = n,
 {
  rw ← neg_inj, rw neg_neg,
  rw ← neg_zero at p2, rw lt_neg at p2,
  exact int.to_nat_of_nonneg (le_of_lt p2),
 },
use j,
cases hg12 with hg1 hg2, 
 {
  use -(g + 1),
  split, exact hg0,
  right, 
  
  rw ← neg_inj at hg1, rw mul_comm at hg1, 
  rw ← neg_mul at hg1, rw coe_coe at hg1, rw mul_comm at hg1,
  nth_rewrite 1 mul_comm at hg1, rw ← neg_mul at hg1, rw neg_add at hg1,
  rw ← sub_eq_add_neg at hg1,
  nth_rewrite 2 mul_comm at hg1, rw ← neg_mul at hg1, nth_rewrite 2 mul_comm at hg1,
  nth_rewrite 1 mul_comm at hg1,

  rw neg_add, nth_rewrite 1 mul_add, rw mul_neg_one, 
  have really : -(3:ℤ) + 2 = -1 := by norm_num,
  rw add_assoc, rw really, rw ← sub_eq_add_neg,
  exact hg1,
 },

 {
  use -(g + 1),
  split, exact hg0,
  left,
 
  rw ← neg_inj at hg2, rw mul_comm at hg2, 
  rw ← neg_mul at hg2, rw coe_coe at hg2, rw mul_comm at hg2,
  nth_rewrite 1 mul_comm at hg2, rw ← neg_mul at hg2, rw neg_add at hg2,
  rw ← sub_eq_add_neg at hg2,
  nth_rewrite 2 mul_comm at hg2, rw ← neg_mul at hg2, nth_rewrite 2 mul_comm at hg2,
  nth_rewrite 1 mul_comm at hg2,

  rw neg_add, nth_rewrite 1 mul_add, rw mul_neg_one,
  have really : -(3:ℤ) + 1 = -2 := by norm_num,
  rw add_assoc, rw really, rw ← sub_eq_add_neg,
  exact hg2,
 },


end

lemma e1 (n : ℕ) : n + n = 2*n :=
begin
have t := two_mul n, exact eq.symm t,
end

lemma e2 (n : ℕ) : n + 1 + n = 2*n + 1 :=
begin
rw add_assoc, nth_rewrite 1 add_comm, rw ← add_assoc, rw (e1 n),
end

lemma e3 (n : ℕ) : n + 1 + (n + 1) = 2*n + 2 :=
begin
have t := two_mul (n + 1), rw ← t, rw mul_add, rw mul_one,
end

lemma e4 (n : ℕ) : 2*n + 2 + n = 3*n + 2 :=
begin
rw add_assoc, rw add_comm 2 n, rw ← add_assoc,
nth_rewrite 1 ← one_mul n, rw ← right_distrib 2 1 n, 
end

lemma e5 (n : ℕ) : 2*n + 1 + n = 3*n + 1 :=
begin
rw add_assoc, rw add_comm 1 n, rw ← add_assoc,
nth_rewrite 1 ← one_mul n, rw ← right_distrib 2 1 n, 
end

lemma unit_pow_expansion (k d : ℕ) (p1 q1 r1 : ℤ) (w : k.succ = d) (p q r : ℤ) 

  (s1 : 7*(3^(2*d)) + (2*p + 12*r)*(3^(2*d + 1)) + (-(4*q) + 2)*(3^d) + (p^2 + 6*(r^2))*(3^(2*d + 2)) + (2*p - 4*q*r)*(3^(d+1)) + 1 = p1) (s2 : 16*(3^(2*d)) + 32*r*(3^(2*d + 1)) - 10*q*(3^d) + (16* r^2)*(3^(2*d + 2)) + (2*q*p - 12*q*r)*(3^(d+1)) + 2*q = q1) (s3 : 5*(3^(2*d)) + (2*p + 8*r)*(3^(2*d + 1)) + (-(6*q) + 2)*(3^d) + (2*r*p + 3*(r^2))*(3^(2*d + 2)) + (-(6*q)*r + 2*r)*(3^(d + 1)) + q^2 = r1) 
  
  (h : ((unit^(3^k.succ)):ℤθ) = ⟨1 + 3^k.succ + (3^(k.succ + 1))*p, q, 3^k.succ + (3^(k.succ + 1))*r⟩) :

  ((unit^(3^(k.succ))):ℤθ) * ((unit^(3^(k.succ))):ℤθ) = ⟨7*(3^(2*d)) + (2*p + 12*r)*(3^(2*d + 1)) + (-(4*q) + 2)*(3^d) + (p^2 + 6*(r^2))*(3^(2*d + 2)) + (2*p - 4*q*r)*(3^(d+1)) + 1 , 16*(3^(2*d)) + 32*r*(3^(2*d + 1)) - 10*q*(3^d) + (16* r^2)*(3^(2*d + 2)) + (2*q*p - 12*q*r)*(3^(d+1)) + 2*q, 5*(3^(2*d)) + (2*p + 8*r)*(3^(2*d + 1)) + (-(6*q) + 2)*(3^d) + (2*r*p + 3*(r^2))*(3^(2*d + 2)) + (-(6*q)*r + 2*r)*(3^(d + 1)) + q^2⟩ :=
  
  begin
  rw w at h, rw w, rw [s1, s2, s3],
  rw h, rw mul_mule_3, dsimp, ring_nf, --how to apply only to lhs?
  
  split,
   {
    repeat {rw [add_mul, mul_assoc]}, repeat {rw ← pow_add}, repeat {rw [(e1 d), (e2 d), (e3 d)]}, repeat {rw ← mul_assoc}, 
    rw ← add_mul (2 * p) (12 * r) (3^( 2 * d + 1)), rw ← add_mul (p^2) (6* r^2) (3^( 2 * d + 2)), rw ← add_mul (-(4*q)) 2 (3^d), 
    repeat {rw ← add_assoc}, 
    rw ← s1, 
   },
  split,
   {
    repeat {rw [add_mul, mul_assoc, sub_mul]}, rw mul_assoc (16* r^2) (3^(d+1)) (3^(d+1)), repeat {rw ← pow_add},
    rw [(e1 d), (e2 d), (e3 d)], rw ← sub_mul (2 * q * p) (12 * q * r) (3^(d+1)), 
    repeat {rw ← add_assoc}, rw add_sub (16*(3^(2*d))) (32 * r * (3^(2 * d + 1))) (10 * q * (3^d)),
    rw ← s2,
   },
   
  repeat {rw [add_mul, mul_assoc]}, repeat {rw ← pow_add},
  rw [(e1 d), (e2 d), (e3 d)], repeat {rw ← mul_assoc},
  rw ← add_mul (2 * p) (8 * r) (3^(2 * d + 1)), rw ← add_mul (-(6 * q)) 2 (3^d), rw ← add_mul (2*r*p) (3* r^2) (3^(2* d + 2)),  rw ← add_mul (-(6 * q) * r) (2*r) (3^(d+1)),
  repeat {rw ← add_assoc},
  rw ← s3,
  end

lemma mul_simp_1 (d : ℕ) (p q r : ℤ) (p3 : ℤ) (t : p = p3):

  (1 + 3 ^ d + 3 ^ (d + 1) * p) * (7 * 3 ^ (2 * d) + (2 * p + 12 * r) * 3 ^ (2 * d + 1) + (-(4 * q) + 2) * 3 ^ d + (p ^ 2 + 6 * r ^ 2) * 3 ^ (2 * d + 2) + (2 * p - 4 * q * r) * 3 ^ (d + 1) + 1)

  + 6 * (3 ^ d + 3 ^ (d + 1) * r) * (5 * 3 ^ (2 * d) + (2 * p + 8 * r) * 3 ^ (2 * d + 1) + (-(6 * q) + 2) * 3 ^ d + (2 * r * p + 3 * r ^ 2) * 3 ^ (2 * d + 2) + (-(6 * q) * r + 2 * r) * 3 ^ (d + 1) + q ^ 2)

  - 2 * q * (5 * 3 ^ (2 * d) + (2 * p + 8 * r) * 3 ^ (2 * d + 1) + (-(6 * q) + 2) * 3 ^ d + (2 * r * p + 3 * r ^ 2) * 3 ^ (2 * d + 2) + (-(6 * q) * r + 2 * r) * 3 ^ (d + 1) + q ^ 2)

  - 2 * (3 ^ d + 3 ^ (d + 1) * r) * (16 * 3 ^ (2 * d) + 32 * r * 3 ^ (2 * d + 1) - 10 * q * 3 ^ d + 16 * r ^ 2 * 3 ^ (2 * d + 2) + (2 * q * p - 12 * q * r) * 3 ^ (d + 1) + 2 * q)

  = p3 :=

begin
ring_nf,
repeat {rw [add_mul, mul_assoc]}, repeat {rw ← pow_add},
repeat {rw [(e1 d), (e2 d), (e3 d)]},

rw ← right_distrib (-(20*q)) 14 (3^(2*d)), rw ← mul_assoc (-(8*q)) p (3^(2*d + 1)), rw ← mul_assoc 4 p (3^(2*d + 1)), rw ← right_distrib (-(8 * q) * p) (4 * p) (3^(2*d + 1)), 
rw ← mul_assoc (-(32*q)) r (3^(2*d + 1)), rw ← mul_assoc 24 r (3^(2*d + 1)), rw ← right_distrib (-(32*q) * r) (24 * r) (3^(2*d + 1)), rw ← right_distrib (-(8 * q) * p + 4 * p) (-(32 * q) * r + 24 * r) (3^(2*d + 1)),

rw ← mul_assoc (3 ^ (2 * d + 2))  p  (p * 3 ^ d), rw mul_comm (3 ^ (2 * d + 2))  p, rw mul_assoc p (3 ^ (2 * d + 2)) (p * 3 ^ d),
rw ← mul_assoc (3 ^ (2 * d + 2)) p (3 ^ d), rw mul_comm (3 ^ (2 * d + 2)) p, rw mul_assoc p (3 ^ (2 * d + 2)) (3^d), rw ← pow_add, rw (e4 d),
rw ← mul_assoc (3 ^ (2*d + 2)) r (p * (3^d)), rw mul_comm (3 ^ (2*d + 2)) r, rw mul_assoc r (3 ^ (2*d + 2)) (p * (3^d)), rw ← mul_assoc (3 ^ (2*d + 2)) p (3^d), rw mul_comm (3 ^ (2*d + 2)) p, rw mul_assoc p (3 ^ (2*d + 2)) (3^d), rw ← pow_add, rw (e4 d),
rw ← mul_assoc  (3 ^ (2 * d + 1))  p (3 ^ d), rw mul_comm (3 ^ (2 * d + 1))  p, rw mul_assoc p (3 ^ (2 * d + 1)) (3 ^ d), rw ← pow_add, rw (e5 d),
sorry
end

lemma unit_pow_expansion_final (k  d : ℕ) (p1 q1 r1 : ℤ) (p2 q2 r2 : ℤ) (w : k.succ = d) (p q r : ℤ) 

  (s1 : 7*(3^(2*d)) + (2*p + 12*r)*(3^(2*d + 1)) + (-(4*q) + 2)*(3^d) + (p^2 + 6*(r^2))*(3^(2*d + 2)) + (2*p - 4*q*r)*(3^(d+1)) + 1 = p1) (s2 : 16*(3^(2*d)) + 32*r*(3^(2*d + 1)) - 10*q*(3^d) + (16* r^2)*(3^(2*d + 2)) + (2*q*p - 12*q*r)*(3^(d+1)) + 2*q = q1) (s3 : 5*(3^(2*d)) + (2*p + 8*r)*(3^(2*d + 1)) + (-(6*q) + 2)*(3^d) + (2*r*p + 3*(r^2))*(3^(2*d + 2)) + (-(6*q)*r + 2*r)*(3^(d + 1)) + q^2 = r1) 

  (a1 : p = p2) (a2 : q = q2) (a3 : r = r2)

  (h : ((unit^(3^k.succ)):ℤθ) = ⟨1 + 3^k.succ + (3^(k.succ + 1))*p, q, 3^k.succ + (3^(k.succ + 1))*r⟩) :

  ((unit^(3^(k.succ + 1))):ℤθ) = ⟨p2 , q2, r2⟩ :=

  begin

  rw [pow_add, pow_mul, pow_one, pow_three],
  have torture := unit_pow_expansion, 
  specialize torture k d p1 q1 r1 w p q r s1 s2 s3 h, 
  rw torture, rw h,  rw w, clear s1 s2 s3 h torture,
  
  rw mul_mule_3, dsimp, 
  ext; dsimp,
  
   {
    sorry
   },

   {
    sorry
   },

  sorry
  end



lemma unit_pow_three_pow (n : ℕ) :
  ∃ (a b c: ℤ), ((((unit^(3^(n+1))):ℤθˣ):ℤθ).f = 1 + (3^(n+1)) + (3^(n+2))*a) ∧ (((unit^(3^(n+1))):ℤθˣ):ℤθ).g = b ∧ (((unit^(3^(n+1)):ℤθˣ):ℤθ).h = (3^(n+1)) + (3^(n+2))*c) :=
  begin
  induction n with k hk,
   {
    rw zero_add, rw zero_add,
    rw pow_one, rw pow_one,
    change ∃ (a b c: ℤ), ((unit:ℤθ)^3).f = 1 + 3 + (3^2)*a ∧ ((unit:ℤθ)^3).g = b ∧ ((unit:ℤθ)^3).h = 3 + (3^2) * c,
    rw unit_cubed, dsimp,
    use (-3), use (-63), use (-2), norm_num,
   },
  have l : k + 1 = k.succ := by refl,
  rw ← one_add_one_eq_two at hk, rw ← add_assoc at hk, rw l at hk,
  cases hk with p hp, cases hp with q hq, cases hq with r hr, cases hr with h1 h23, cases h23 with h2 h3,
  have t : ((unit^(3^k.succ)):ℤθ) = ⟨1 + 3^k.succ + (3^(k.succ + 1))*p, q, 3^k.succ + (3^(k.succ + 1))*r⟩,
   {
    ext; dsimp,
    exact_mod_cast h1, exact_mod_cast h2, exact_mod_cast h3,
   },
  

  sorry
  end




theorem units (a : (ℤθ)ˣ) (h : a.val.h = 0) :
  a = 1 ∨ a = -1 :=
  begin
  have l : ∃n : ℤ, a = unit^n ∨ a = -unit^n := units_are a,
  cases l with t ht,
  have stove := int.div_add_mod t 3,
  have lower := int.mod_nonneg t (by dec_trivial : (3:ℤ) ≠0 ),
  have upper := int.mod_lt_of_pos t (by dec_trivial : (3:ℤ) > 0 ),
  interval_cases using lower upper,
  clear stove lower upper,
  {
   have r := y_mod_three t 0 h_1,
   cases r with j hj,
   rw add_zero at hj,
   
   cases ht with hf hd,
   {
    
    sorry,
   },
   sorry,
  },
  {
   cases ht with hf hd,
   {
    exfalso,
    have g := y_mod_three t 1 h_1,
    cases g with p hp,
    have hg := unit_zpow_one_mod_three,
    specialize hg p,
    rw ← hp at hg,
    cases hg with g1 g23,
    cases g23 with g2 g3,
    rw ← hf at g3,
    have sd : a.val.h = (a:ℤθ).h := by refl,
    rw ← sd at g3, rw h at g3,
    norm_num at g3,
    --change the rest!
   },
  exfalso,
  have g := y_mod_three t 1 h_1,
  cases g with p hp,
  have hg := unit_zpow_one_mod_three,
  specialize hg p,
  rw ← hp at hg,
  cases hg with g1 g23,
  cases g23 with g2 g3, 
  have hf := y_mod_three (((unit^t):ℤθˣ):ℤθ).h 2 g3,
  cases hf with r hr,
  rw ← neg_eq_iff_eq_neg at hd,
  rw ← hd at hr, 
  rw ← neg_inj at h, rw neg_zero at h, 
  have sd : -(a.val.h) = ((-a):ℤθ).h := by refl,
  rw sd at h, norm_cast at h,
  rw h at hr,
  rw ← add_neg_eq_iff_eq_add at hr, rw zero_add at hr,
  rw ← neg_inj at hr, rw neg_neg at hr, rw mul_comm at hr, rw ← neg_mul at hr, 
  have final := eq.symm hr,
  have line := dvd_of_mul_left_eq (-r) final,
  norm_num at line,
  },
  {
   cases ht with hf hd,
   {
    exfalso,
    have g := y_mod_three t 2 h_1,
    cases g with p hp,
    have hg := unit_zpow_two_mod_three,
    specialize hg p,
    rw ← hp at hg,
    cases hg with g1 g23,
    cases g23 with g2 g3, 
    have hf := y_mod_three (((unit^t):ℤθˣ):ℤθ).h 2 g3,
    cases hf with r hr,
    rw ← hf at hr,
    have sd : a.val.h = (a:ℤθ).h := by refl,
    rw sd at h,
    rw h at hr,
    rw ← add_neg_eq_iff_eq_add at hr, rw zero_add at hr,
    rw ← neg_inj at hr, rw neg_neg at hr, rw mul_comm at hr, rw ← neg_mul at hr, 
    have final := eq.symm hr,
    have line := dvd_of_mul_left_eq (-r) final,
    norm_num at line,
   },
  exfalso,
  have g := y_mod_three t 2 h_1,
  cases g with p hp,
  have hg := unit_zpow_two_mod_three,
  specialize hg p,
  rw ← hp at hg,
  cases hg with g1 g23,
  cases g23 with g2 g3, 
  have hf := y_mod_three (((unit^t):ℤθˣ):ℤθ).h 2 g3,
  cases hf with r hr,
  rw ← neg_eq_iff_eq_neg at hd,
  rw ← hd at hr, 
  rw ← neg_inj at h, rw neg_zero at h, 
  have sd : -(a.val.h) = ((-a):ℤθ).h := by refl,
  rw sd at h, norm_cast at h,
  rw h at hr,
  rw ← add_neg_eq_iff_eq_add at hr, rw zero_add at hr,
  rw ← neg_inj at hr, rw neg_neg at hr, rw mul_comm at hr, rw ← neg_mul at hr, 
  have final := eq.symm hr,
  have line := dvd_of_mul_left_eq (-r) final,
  norm_num at line,
  },
  end




end ℤθ