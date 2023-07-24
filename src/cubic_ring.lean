import
  tactic
  data.complex.basic
  algebra.euclidean_domain.basic
  algebra.group.defs
  algebra.group_power.ring
  algebra.group_power.basic
  data.real.irrational
  algebra.order.monoid.lemmas

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

def Norm : ℤθ → ℤ := λ k, | k.f^3 - 2*k.g^3 + 4*k.h^3 - 3*k.f^2*k.g - 3*k.f^2*k.h + 6*k.f*k.g^2 + 6*k.g^2*k.h + 24*k.f*k.h^2 - 12*k.g*k.h^2 - 12*k.f*k.g*k.h |

def unit : (ℤθ)ˣ := ⟨ -1 - 3*θ - θ^2 , 25 + 13 * θ + 5 * θ^2, by ext; dec_trivial, by ext; dec_trivial ⟩

lemma unit_l : (unit:ℤθ) = ⟨-1, -3, -1⟩ :=
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

--this is to be left for later
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

lemma unit_cubed : (unit:ℤθ)^3 = ⟨-23, -63, -15⟩ :=
begin
rw pow_three,
nth_rewrite 1 unit_l, nth_rewrite 1 unit_l,
nth_rewrite 1 mul_mule_3,
dsimp, ring_nf,
end

lemma unit_pow_zero : ((((unit^(3*0)):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*0)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*0)):ℤθˣ):ℤθ)).h % 3 = 0 :=
begin
split,
refl,
split,
refl, refl,
end

lemma unit_pow_zero_mod_three : ∀(k:ℕ), (((((unit^(3*k)):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*k)):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*k)):ℤθˣ):ℤθ)).h % 3 = 0) ∧ (((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).f % 3 = 1 ∧ ((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).g % 3 = 0 ∧ ((((unit^(3*-(k:ℤ))):ℤθˣ):ℤθ)).h % 3 = 0) :=
begin
intro k,
split,
{
  induction k using nat.strong_induction_on with b hb,
  dsimp at hb,
  have j : b = 0 ∨ 0 < b,
  {

    sorry,
  },
  cases j with hy hr,
  {
    rw hy,
    exact unit_pow_zero,
  },
  specialize hb (b-1),
  have f : 0 < 1 := by dec_trivial,
  have z := nat.sub_lt hr f,
  have t : ((unit ^ (3 * (b - 1))):ℤθ).f % 3 = 1 ∧ ((unit ^ (3 * (b - 1))):ℤθ).g % 3 = 0 ∧ ((unit ^ (3 * (b - 1))):ℤθ).h % 3 = 0,
  {
    norm_cast,
    apply hb,
    exact z,
  },
  norm_cast at t,
  clear hb z f,
  cases t with t1 t23,
  cases t23 with t2 t3,
  have g1 : ((unit:ℤθ) ^ (3 * (b - 1))).f % 3 = 1,
  {
    norm_cast,
    exact t1,
  },
  have r1 := y_mod_three ((unit ^ (3 * (b - 1))):ℤθ).f 1 g1,
  cases r1 with c1 hc1,
  have g2 : ((unit:ℤθ) ^ (3 * (b - 1))).g % 3 = 0,
  {
    norm_cast,
    exact t2,
  },
  have r2 := y_mod_three ((unit ^ (3 * (b - 1))):ℤθ).g 0 g2,
  cases r2 with c2 hc2,
  have g3 : ((unit:ℤθ) ^ (3 * (b - 1))).h % 3 = 0,
  {
    norm_cast,
    exact t3,
  },
  have r3 := y_mod_three ((unit ^ (3 * (b - 1))):ℤθ).h 0 g3,
  cases r3 with c3 hc3,
  rw add_zero at hc2,
  rw add_zero at hc3,
  have s : ((unit ^ (3 * (b - 1))):ℤθ) = ⟨3*c1 + 1, 3*c2, 3*c3⟩,
  {
    ext; dsimp,
    exact hc1, exact hc2, exact hc3,
  },
  have s1 : ((unit ^ (3 * (b))):ℤθ) = ((unit ^ (3 * (b - 1))):ℤθ) * (((unit ^ (3))):ℤθ),
  {
    rw ← pow_add,
    --rw mul_sub_one,
    sorry,
  },
  rw s at s1,
  rw unit_cubed at s1,
  rw mul_mule_3 at s1,
  dsimp at s1,
  ring_nf at s1,
  --special rw command
  sorry,
},

sorry,
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
   cases ht with hf hd,
   {
    have r := y_mod_three t 0 h_1,
    cases r with j hj,
    rw add_zero at hj,
    sorry,
   },
   sorry,
  },
  {
   cases ht with hf hd,
   {

    sorry,
   },
   sorry,
  },
  {
   cases ht with hf hd,
   {

    sorry,
   },
   sorry,
  },
  end




end ℤθ