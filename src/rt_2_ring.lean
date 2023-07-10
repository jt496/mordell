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

--We will be considering quadratic integers of the form `x+y*α`, where `α=√2`
--and `x y : ℤ`. We shall write `ℤα` for the Type of these integers,
--and represent them by their z- and w-coordinates.


@[ext]
structure ℤα : Type :=
  (z : ℤ)
  (w : ℤ)

namespace ℤα 



--We give lean a method for checking whether two such integers are equal.

noncomputable
instance dec_eq : decidable_eq ℤα := infer_instance

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

--We give lean a way of displaying elements of `ℤα` using the command `#eval`.
--TO DO : rewrite this using pattern matching.

def repr (a : ℤα) : string :=
begin
  by_cases a.z=0,
  {
    by_cases a.w=0,
    { exact "0" },
    { exact a.w.repr ++ " * α" }
  },
  {
    by_cases a.w=0,
    { exact a.z.repr },
    {
      by_cases a.w > 0,
      { exact a.z.repr ++ " + " ++ a.w.repr ++ " * α" },
      { exact a.z.repr ++ " - " ++ (-(a.w)).repr ++ " * α" }
    }
  }
end

instance ℤα_repr : has_repr ℤα :=
{ repr := repr }

-- #eval (⟨1, 2⟩:ℤα) 
-- #eval (⟨0,0⟩:ℤα)
-- #eval (⟨-4,0⟩:ℤα)
-- #eval (⟨0,-5⟩:ℤα)

/-- Defining addition, multiplication and other things needed for rings-/

def zero : ℤα := ⟨0,0⟩  
def one : ℤα := ⟨1,0⟩
def α : ℤα := ⟨0,1⟩
def add : ℤα → ℤα → ℤα := λ a b, ⟨ a.z+b.z, a.w+b.w ⟩
def neg : ℤα → ℤα := λ a, ⟨ -a.z, -a.w ⟩

/--Using the fact that α^2 = α - 2, we obtain the rule for multiplication-/

def mul : ℤα → ℤα → ℤα := λ a b, ⟨ a.z*b.z + 2*a.w*b.w, a.z*b.w + a.w*b.z⟩

variables a b c : ℤα  

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
  split;
  ring,
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
  split;
  ring,
end

lemma my_right_distrib : mul (add a b) c = add (mul a c) (mul b c) :=
begin
  cases a, cases b, cases c,
  simp only [mul,add],
  split;
  ring,
end

lemma my_mul_comm : mul a b = mul b a :=
begin
  cases a, cases b,
  simp only [mul],
  split; ring,
end

def zsmul : ℤ → ℤα → ℤα := λ n a, ⟨n*a.z, n*a.w⟩

lemma my_zsmul_zero' : ∀ (a : ℤα), zsmul (0:ℤ)  a = (zero) :=
begin
intro a,
unfold zsmul,
rw zero_mul,
rw zero_mul,
rw ← zero,
end

lemma my_zsmul_succ' : ∀ (n : ℕ) (a : ℤα), zsmul (int.of_nat n.succ) a = a.add (zsmul (int.of_nat n) a) :=
begin
intros n a,
change (⟨int.of_nat n.succ*a.z, int.of_nat n.succ*a.w⟩:ℤα) = (⟨a.z + int.of_nat n*a.z, a.w + int.of_nat n*a.w⟩:ℤα),
norm_num,
split,
linarith,
linarith,
end

lemma my_zsmul_neg' : ∀ (n : ℕ) (a : ℤα), zsmul -[1+ n] a = (zsmul ↑(n.succ) a).neg :=
begin
intros n a,
simp,
change (⟨int.neg_succ_of_nat n*a.z, int.neg_succ_of_nat n*a.w⟩:ℤα) = (⟨-(int.of_nat n.succ*a.z), -(int.of_nat n.succ*a.w)⟩:ℤα),
simp,
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

def int_cast : ℤ → ℤα := λ a, ⟨a, 0⟩ 
def nat_cast : ℕ → ℤα := λ a, ⟨a, 0⟩

lemma my_nat_cast_zero : nat_cast 0 = zero :=
begin
unfold nat_cast,
rw int.coe_nat_zero,
refl,
end

lemma my_nat_cast_succ : ∀ (n : ℕ), nat_cast (n + 1) = (nat_cast n).add one :=
begin
intro n,
change (⟨int.of_nat (n+1), 0⟩:ℤα) = (⟨int.of_nat n + 1, 0⟩:ℤα),
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

/-- Making ℤα into a ring-/

instance is_ring : comm_ring ℤα :=
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

  --If the below lemmas are commented out, suddenly lean can infer that
  --ℤα is a PID again.
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

--#eval α^3

open real int

@[reducible]
noncomputable
def rt_2 : ℝ  := real.sqrt 2

@[simp]
lemma rt_2_sq : rt_2^2 = 2 :=
begin
  have : (0:ℝ) ≤ 2 := by norm_num,
  rw pow_two,
  rw ← real.sqrt_mul this 2,
  rw real.sqrt_mul_self this,
end

lemma sqrt_2_inv_mul_self : rt_2⁻¹ * rt_2 = 1 :=
begin
  apply inv_mul_cancel,
  intro h,
  have := real.sqrt_eq_iff_mul_self_eq (_ : 0 ≤ 2) (_ : 0 ≤ 0 ),
  rw this at h,
  norm_num at h,
  norm_num,
  refl,
end

noncomputable
def to_ℝ : ℤα → ℝ := λ a, a.z + a.w * rt_2

lemma my_map_one : to_ℝ one = 1 :=
begin
  simp only [to_ℝ,one],
  dsimp,
  norm_num,
end

lemma my_map_mul : to_ℝ (mul a b) = (to_ℝ a) * (to_ℝ b) :=
begin
  cases a, cases b,
  simp only [mul,to_ℝ],
  dsimp,
  norm_num,
  ring_nf,
  congr,
  rw rt_2,
  norm_num,
end

lemma my_map_zero : to_ℝ zero = 0 :=
begin
  simp [to_ℝ,zero],
  dsimp,
  norm_cast,
  ring_nf,
end

lemma my_map_add : to_ℝ (add a b) = (to_ℝ a) + (to_ℝ b) :=
begin
  cases a, cases b,
  simp only [add,to_ℝ],
  dsimp,
  norm_num,
  ring_nf,
end 

noncomputable
def inclusion : ℤα →+* ℝ :=
{ to_fun := to_ℝ ,
  map_one' := my_map_one,
  map_mul' := my_map_mul,
  map_zero' := my_map_zero,
  map_add' := my_map_add }

noncomputable
instance ℤα_coe_to_ℝ : has_coe ℤα ℝ :=
{ coe := inclusion.to_fun }

lemma coe_of_mk (x y : ℤ):
  ((ℤα.mk x y) : ℝ) = (x + y * real.sqrt 2) :=
begin
  change to_ℝ ⟨ x, y ⟩ =  x + y*rt_2,
  unfold to_ℝ,
end

def Norm : ℤα → ℤ :=
  λ z, abs(z.z^2 - 2*z.w^2)

def Q_Norm : ℚ → ℚ → ℚ :=
  λ a b, abs(a^2 - 2*b^2) 

lemma Q_Norm_mul (a b c d : ℚ): Q_Norm a b * Q_Norm c d = Q_Norm (a*c + 2*b*d) (a*d + b*c) :=
begin
unfold Q_Norm,
rw ← abs_mul,
ring_nf,
end

lemma Q_Norm_coe (a : ℤα) : Q_Norm (a.z:ℚ) (a.w:ℚ) = ((Norm a):ℚ) :=
begin
 unfold Q_Norm Norm,
 norm_cast,
end

lemma Norm_mul : Norm (a*b) = Norm a * Norm b :=
begin
unfold Norm,
change |(a.z*b.z + 2*a.w*b.w) ^ 2 - 2 * (a.z*b.w + a.w*b.z) ^ 2| = |a.z ^ 2 - 2 * a.w ^ 2| * |b.z ^ 2 - 2 * b.w ^ 2|,
rw ← abs_mul,
ring_nf,
end

lemma Norm_eq_zero_iff : Norm a = 0 ↔ a = 0 :=
begin
split,
{
 intro h,
 unfold Norm at h,
 have g : a.w = 0 ∨ a.w ≠ 0 := by omega, 
 cases g with r t,
 {
  rw r at h,
  ring_nf at h,
  rw abs_sq at h,
  rw sq_eq_zero_iff at h,
  ext,
  exact h,
  exact r,
 },
 --a.w neq 0
 have k : (a.w:ℝ)^2 ≠ 0,
 {
  intro h,
  apply t,
  rw ← sq_eq_zero_iff, 
  exact_mod_cast h,
 },

 have l : ((a.z:ℝ)/a.w)^2 = 2,
  {
    rw ← add_left_inj (2 * a.w ^ 2) at h,
    ring_nf at h,
    rw ← mul_left_inj' k,
    rw div_pow (a.z:ℝ) (a.w:ℝ) 2,
    ring_nf,
    nth_rewrite 1 mul_comm,
    rw inv_mul_cancel k,
    rw one_mul,
    norm_cast,
    rw add_comm at h,
    rw add_left_eq_self at h,
    rw abs_eq_zero at h,
    rw sub_eq_zero at h,
    exact h,
  },
exfalso,
have big : (0:ℝ) ≤ 2 := zero_le_two,
have large : (0:ℝ) ≤ ((a.z:ℝ) / (a.w:ℝ)) ^ 2 := sq_nonneg ((a.z:ℝ) / (a.w:ℝ)),
rw ← real.sqrt_inj large big at l,

have obese := irrational_sqrt_two,
rw irrational_iff_ne_rational at obese,
specialize obese (abs(a.z)) (abs(a.w)),
apply obese,
rw ← l,
rw real.sqrt_sq_eq_abs,
rw abs_div,
norm_cast,
},

intro h,
unfold Norm,
rw h,
ring_nf,
end

--need to define integer closest to real number 
--noncomputable
def nearest_ℤ (z : ℚ) : ℤ :=
  round (z) 

def nearest_ℤα (a : ℚ × ℚ) : ℤα :=
  ⟨round a.1, round a.2⟩ 

--noncomputable
def ex_div : ℤα → ℤα → (ℚ × ℚ) :=
  λ a b, ⟨(a.z*b.z - 2*a.w*b.w)/(b.z^2 - 2*b.w^2) , (a.w*b.z - a.z*b.w)/(b.z^2 - 2*b.w^2)⟩

def div : ℤα → ℤα → ℤα :=
  λ a b, nearest_ℤα (ex_div a b)

lemma re_sub_nearest (z : ℚ) :
  (z - nearest_ℤ z)^2 ≤ (2⁻¹)^2 :=
begin
 rw sq_le_sq,
 unfold nearest_ℤ,
 have : | (1/2 : ℚ) | = 1/2 :=
    by simp only [one_div, abs_eq_self, inv_nonneg,
                  zero_le_bit0, zero_le_one],
 ring_nf,
 rw this,
 exact abs_sub_round z,
end

--noncomputable
def mod : ℤα → ℤα → ℤα :=
  λ a b, a - b * (div a b)

--noncomputable
instance has_mod_ℤα : has_mod ℤα :=
{ mod := mod }

--noncomputable
instance has_div_ℤα : has_div ℤα := { div := div }

theorem div_add_mod (a b : ℤα):
  b *(a/b) + (a%b) = a :=
begin
  change b * div a b + mod a b = a,
  simp [mod],
end

lemma ineq_nearest_1 (f g : ℤα) : ((f.ex_div g).fst - ↑((f.div g).z))^2 ≤ 1/4 :=
begin
unfold div,
unfold nearest_ℤα,
dsimp,
have g := abs_sub_round (f.ex_div g).fst,
have k : |1/2| = (1/2:ℚ) := abs_of_pos one_half_pos,
rw ← k at g,
rw ← sq_le_sq at g,
norm_num at g,
exact g,
end

lemma ineq_nearest_2 (f g : ℤα) : 2*((f.ex_div g).snd - ↑((f.div g).w))^2 ≤ 1/2 :=
begin
unfold div,
unfold nearest_ℤα,
dsimp,
have g := abs_sub_round (f.ex_div g).snd,
have k : |1/2| = (1/2:ℚ) := abs_of_pos one_half_pos,
rw ← k at g,
rw ← sq_le_sq at g,
have s : ((0:ℚ) < 2) := two_pos,
rw ← mul_le_mul_left s at g,
norm_num at g,
exact g,
end

lemma ineq (f g : ℤα): Q_Norm ((ex_div f g).1 - ((div f g).z : ℚ)) ((ex_div f g).2 - ((div f g).w : ℚ)) ≤ 3/4 :=
begin 
unfold Q_Norm,
have r := abs_sub (((f.ex_div g).fst - ↑((f.div g).z)) ^ 2) (2 * ((f.ex_div g).snd - ↑((f.div g).w)) ^ 2),
rw abs_sq ((f.ex_div g).fst - ↑((f.div g).z)) at r,
rw abs_mul 2 (((f.ex_div g).snd - ↑((f.div g).w))^2) at r,
rw abs_two at r,
rw abs_sq ((f.ex_div g).snd - ↑((f.div g).w)) at r,
have b := add_le_add (ineq_nearest_1 f g) (ineq_nearest_2 f g),
norm_num at b,
exact le_trans r b,
end

lemma simp_1 (a b : ℤα) (j : Norm b ≠ 0) :  (b.z:ℚ) * (((a.z:ℚ) * (b.z:ℚ) - 2 * ↑(a.w) * ↑(b.w)) / (↑(b.z) ^ 2 - 2 * ↑(b.w) ^ 2) - ↑((a.div b).z)) + 2 * ↑(b.w) * ((↑(a.w) * ↑(b.z) - ↑(a.z) * ↑(b.w)) / (↑(b.z) ^ 2 - 2 * ↑(b.w) ^ 2) - ↑((a.div b).w)) = (a.z - b.z*((a.div b).z) - 2*b.w*((a.div b).w) ) :=
begin
repeat {rw mul_sub_left_distrib},
rw add_sub_assoc',
rw add_comm,
rw add_sub,
repeat {rw sub_left_inj},
repeat {rw mul_div},
repeat {rw mul_sub_left_distrib},
rw ← add_div,
unfold Norm at j,
have w : ((b.z:ℚ) ^ 2 - 2 * (b.w) ^ 2) ≠ 0,
{
  by_contra,
  apply j,
  norm_cast at h,
  rwa ← abs_eq_zero at h,
},
rw div_eq_iff w,
ring_nf,
end

lemma simp_2 (a b : ℤα) (j : Norm b ≠ 0) : (b.z:ℚ) * (((a.w) * ↑(b.z) - ↑(a.z) * ↑(b.w)) / (↑(b.z) ^ 2 - 2 * ↑(b.w) ^ 2) - ↑((a.div b).w)) + ↑(b.w) * ((↑(a.z) * ↑(b.z) - 2 * ↑(a.w) * ↑(b.w)) / (↑(b.z) ^ 2 - 2 * ↑(b.w) ^ 2) - ↑((a.div b).z)) = (a.w - b.z*((a.div b).w) - b.w*((a.div b).z) ) :=
begin
repeat {rw mul_sub_left_distrib},
rw add_sub_assoc',
rw add_comm,
rw add_sub,
repeat {rw sub_left_inj},
repeat {rw mul_div},
repeat {rw mul_sub_left_distrib},
rw ← add_div,
unfold Norm at j,
have w : ((b.z:ℚ) ^ 2 - 2 * (b.w) ^ 2) ≠ 0,
{
  by_contra,
  apply j,
  norm_cast at h,
  rwa ← abs_eq_zero at h,
},
rw div_eq_iff w,
ring_nf,
end

theorem Norm_sq_mod_lt (h : b ≠ 0) : Norm (mod a b) < Norm b :=
begin
  suffices h : (((a.mod b).Norm):ℚ) < b.Norm,
  exact_mod_cast h,
  rw ← Q_Norm_coe (a.mod b),
  rw ← Q_Norm_coe b,
  have suck : Norm b ≠ 0,{
    by_contra p,
    apply h,
    rwa Norm_eq_zero_iff b at p,
  },
  have s : (0:ℚ) < Q_Norm b.z b.w, {
    unfold Q_Norm,
    norm_cast,
    have jack := abs_nonneg ((b.z) ^ 2 - 2 * (b.w) ^ 2),
    unfold Norm at suck,
    exact lt_of_le_of_ne' jack suck,
  },
  have boing := ineq a b,
  rw ← mul_le_mul_left s at boing,
  rw Q_Norm_mul at boing,
  unfold ex_div at boing,
  dsimp at boing,
  rw simp_1 a b suck at boing,
  rw simp_2 a b suck at boing,
  unfold mod,
  norm_cast at boing,
  have bruh : (a - b * a.div b).z = a.z - b.z * (a.div b).z - 2 * b.w * (a.div b).w,
  {
    change ((⟨a.z - (b.z * (a.div b).z + 2 * b.w * (a.div b).w), a.w - (b.z * (a.div b).w + b.w * (a.div b).z)⟩:ℤα)).z = a.z - b.z * (a.div b).z - 2 * b.w * (a.div b).w,
    dsimp,
    rw sub_add_eq_sub_sub,
  },
  rw ← bruh at boing,
  have sis : (a - b * a.div b).w = a.w - b.z * (a.div b).w - b.w * (a.div b).z,
  {
    change (⟨a.z - (b.z * (a.div b).z + 2 * b.w * (a.div b).w), a.w - (b.z * (a.div b).w + b.w * (a.div b).z)⟩:ℤα).w = a.w - b.z * (a.div b).w - b.w * (a.div b).z,
    dsimp,
    rw sub_add_eq_sub_sub,
  },
  rw ← sis at boing,
  have father : Q_Norm ↑(b.z) ↑(b.w) * (3 / 4) < Q_Norm ↑(b.z) ↑(b.w),
  { 
    nth_rewrite 1 ← mul_one (Q_Norm ↑(b.z) ↑(b.w)), 
    rw mul_lt_mul_left s,
    norm_num,
  },
  exact lt_of_le_of_lt boing father,
end

lemma my_quotient_zero : div a 0 = 0 :=
begin
  unfold div,
  unfold ex_div,
  norm_cast,
  change nearest_ℤα (rat.mk (a.z * (0:ℤ) - 2 * a.w * (0:ℤ)) ((0:ℤ) ^ 2 - 2 * (0:ℤ) ^ 2), rat.mk (a.w * (0:ℤ) - a.z * (0:ℤ)) ((0:ℤ) ^ 2 - 2 * (0:ℤ) ^ 2)) = 0,
  norm_num,
  unfold nearest_ℤα,
  dsimp,
  have l : round (0:ℚ) = (0:ℤ) := round_zero,
  rw l,
  refl,
end

lemma my_mul_left_not_lt (hb : b ≠ 0) :
  ¬ (Norm (a*b) < Norm a) :=
begin
  rw Norm_mul,
  intro h,
  apply hb, clear hb,
  rw ← Norm_eq_zero_iff,
  nth_rewrite 1 ← mul_one a.Norm at h,
  have bob : 0 ≤ a.Norm := abs_nonneg _,
  have rob := lt_or_eq_of_le bob,
  cases rob with rh th,
  rw mul_lt_mul_left rh at h,
  have pob : 0 ≤ b.Norm := abs_nonneg _,
  linarith, --come back and simplify
  exfalso,
  rw ← th at h,
  rw zero_mul at h,
  rw zero_mul at h,
  apply lt_irrefl (0:ℤ),
  exact h,
end

--noncomputable
instance euclidean_ℤα : euclidean_domain ℤα :=
{
--   add := add,
--   zero := ⟨0,0⟩,
--   zero_add := zero_add,
--   add_zero := add_zero,
--   add_assoc := add_assoc,
--   neg := neg,
--   add_left_neg := add_left_neg,
--   add_comm := add_comm,
--   one := ⟨1,0⟩,
--   mul := mul,
--   mul_assoc := mul_assoc,
--   one_mul := one_mul,
--   mul_one := mul_one,
--   left_distrib := left_distrib,
--   right_distrib := right_distrib,
--   mul_comm := mul_comm,
exists_pair_ne := begin
    use 0,
    use 1,
    intro h,
    rw ext_iff at h,
    cases h with h1 h2,
    cases h1,
  end,
  quotient := div,
  quotient_zero := my_quotient_zero,
  remainder := mod,
  quotient_mul_add_remainder_eq := div_add_mod,
  r := λ a b, Norm a < Norm b,
  r_well_founded := begin
    refine inv_image.wf (λ (a₁ : ℤα), Norm a₁) _,
    exact { apply := _ },
    sorry,
  --exact well_founded_lt.apply,
  --What does this mean?
  end,
  remainder_lt := λ a b, by simpa using Norm_sq_mod_lt a b,
  mul_left_not_lt := my_mul_left_not_lt,
}

open euclidean_domain

/- Here is Bezout's theorem for ℤα. -/
#check euclidean_domain.gcd_eq_gcd_ab a b

/- Alternatively, we can prove it ourselves. -/
theorem Bezout (a b : ℤα) :
  ∃ h k : ℤα , h*a + k*b = gcd a b :=
begin
  apply gcd.induction a b,
  {
    intro a,
    use 0,
    use 1,
    rw gcd_zero_left a,
    rw [_root_.mul_zero,_root_.zero_add,_root_.one_mul],
  },
  {
    intros a b ha hab,
    rw gcd_val,
    rcases hab with ⟨ r,  s, hrs⟩,
    use s - r * (b/a),
    use r,
    rw ← hrs, clear hrs,
    have := div_add_mod b a,
    nth_rewrite 1 ← this,
    ring,
  }
end


end ℤα 
