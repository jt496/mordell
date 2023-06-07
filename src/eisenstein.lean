import
  tactic
  data.complex.basic
  algebra.euclidean_domain.basic

/--Just checking if I can push to Github... Yay it worked
An Eisenstein integer is a number of the form `x+y*ω`, where `ω=e^(2*π*i/3)`
and `x y :ℤ`.
We shall write `ℤω` for the Type of Eisenstein integers, with an Eisenstein
integer represented by its x- and y-coordinates.
-/

@[ext]
structure ℤω : Type :=
  (x : ℤ)
  (y : ℤ)


namespace ℤω

/--
We give lean a method for checking whether two Eisenstein integers are equal.
-/
instance dec_eq : decidable_eq ℤω := λ a b,
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

#check nat.add

/--
We give lean a way of displaying elements of `ℤω` using the command `#eval`.
TO DO : rewrite this using pattern matching.
-/
def repr (a : ℤω) : string :=
begin
  by_cases a.x=0,
  {
    by_cases a.y=0,
    { exact "0" },
    { exact a.y.repr ++ " * ω" }
  },
  {
    by_cases a.y=0,
    { exact a.x.repr },
    {
      by_cases a.y > 0,
      { exact a.x.repr ++ " + " ++ a.y.repr ++ " * ω" },
      { exact a.x.repr ++ " - " ++ (-(a.y)).repr ++ " * ω" }
    }
  }
end

instance ℤω_repr : has_repr ℤω :=
{ repr := repr }

#eval (⟨1, 2⟩:ℤω) 
#eval (⟨0,0⟩:ℤω)
#eval (⟨-4,0⟩:ℤω)
#eval (⟨0,-5⟩:ℤω)
#eval (⟨3,-5⟩:ℤω)

/-
To make `ℤω` into a ring, we need to define addition and
multiplication operations, as well as zero and one elements.
Lean also requires some other operations, such as ways
to coerce a natural number or integer into ℤω.
-/
def zero : ℤω := ⟨0,0⟩
def one : ℤω := ⟨1,0⟩ 
def ω : ℤω := ⟨ 0,1 ⟩
def add : ℤω → ℤω → ℤω := λ a b, ⟨ a.x+b.x, a.y+b.y ⟩
def neg : ℤω → ℤω := λ a, ⟨ -a.x, -a.y ⟩
/--
Note that `ω^2 = -ω-1`, so multiplication should be given by the formula

  `(a.x + a.y*ω) * (b.x + b.y*ω) = (a.x*b.x - a.y*b.y) + (a.x*b.y + a.y*b.x -a.y*b.y) * ω`.
-/
def mul : ℤω → ℤω → ℤω := λ a b, ⟨ a.x*b.x - a.y*b.y, a.x*b.y + a.y*b.x - a.y*b.y ⟩



/-
In order to make lean recognize `ℤω` as a ring, we need to supply
proofs of each of the ring axioms.
-/

variables a b c : ℤω 

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
/--
We now package all of this information together to
tell lean that `ℤω` is a ring.
-/
instance is_ring : comm_ring ℤω :=
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
  mul_comm := my_mul_comm
}

/-
We can now use lean as a calculator in the ring `ℤω`.
-/
#eval ω^3
#eval ω^2 + ω + 1


----------------------------------------



open complex int

@[reducible]
noncomputable
def rt_3 : ℝ  := real.sqrt 3


@[simp]
lemma rt_3_sq : rt_3^2 = 3 :=
begin
  have : (0:ℝ) ≤ 3 := by norm_num,
  rw pow_two,
  rw ← real.sqrt_mul this 3,
  rw real.sqrt_mul_self this,
end

@[simp]
lemma sqrt_3_inv_mul_self :
  rt_3⁻¹ * rt_3 = 1 :=
begin
  apply inv_mul_cancel,
  intro h,
  have := real.sqrt_eq_iff_mul_self_eq (_ : 0 ≤ 3) (_ : 0 ≤0 ),
  rw this at h,
  norm_num at h,
  norm_num,
  refl,
end

noncomputable
def complex_ω : ℂ := ⟨ -1/2,  rt_3 / 2 ⟩  


@[simp]
lemma complex_ω_sq : complex_ω^2 = - complex_ω - 1 :=
begin
  rw pow_two,
  ext,
  {
    simp only [complex.mul_re],
    simp only [complex_ω],
    ring_nf,
    rw rt_3_sq,
    norm_num,
  },
  {
    rw complex.mul_im,
    simp only [complex_ω],
    ring_nf,
    dsimp,
    ring_nf,
  },  
end

noncomputable
def to_ℂ : ℤω → ℂ := λ a, a.x + a.y * complex_ω

lemma my_map_one : to_ℂ one = 1 :=
begin
  simp only [to_ℂ,one],
  dsimp,
  norm_num,
end

lemma my_map_mul : to_ℂ (mul a b) = (to_ℂ a) * (to_ℂ b) :=
begin
  cases a, cases b,
  simp only [mul,to_ℂ],
  dsimp,
  norm_num,
  ring_nf,
  congr,
  rw complex_ω_sq,
end

lemma my_map_zero : to_ℂ zero = 0 :=
begin
  simp [to_ℂ,zero],
  dsimp,
  norm_cast,
  ring_nf,
end

lemma my_map_add : to_ℂ (add a b) = (to_ℂ a) + (to_ℂ b) :=
begin
  cases a, cases b,
  simp only [add,to_ℂ,complex_ω],
  ext; dsimp; norm_num; ring,
end 

noncomputable
def inclusion : ℤω →+* ℂ :=
{ to_fun := to_ℂ ,
  map_one' := my_map_one,
  map_mul' := my_map_mul,
  map_zero' := my_map_zero,
  map_add' := my_map_add }

noncomputable
instance ℤω_coe_to_ℂ : has_coe ℤω ℂ :=
{ coe := inclusion.to_fun }

-- @[simp]
lemma coe_of_mk (x y : ℤ):
  ((ℤω.mk x y) : ℂ) = complex.mk (x-y/2:ℝ) (y*rt_3/2:ℝ) :=
begin
  change to_ℂ ⟨ x, y ⟩ = ⟨ x-y/2, y*rt_3/2⟩,
  unfold to_ℂ,
  dsimp,
  unfold complex_ω,
  ext,
  {
    simp only [add_re, int_cast_re, mul_re, int_cast_im, zero_mul, tsub_zero],
    ring,
  },
  {
    simp only [add_im, int_cast_im, mul_im, int_cast_re, zero_mul, add_zero, zero_add, mul_eq_mul_left_iff, cast_eq_zero],
    ring,
  }
end

-- @[simp]
lemma re_of_coe :
  (a:ℂ).re = a.x - a.y/2 :=
begin
  change (to_ℂ a).re = a.x - a.y/2,
  unfold to_ℂ,
  unfold complex_ω,
  simp only [add_re, int_cast_re, mul_re, int_cast_im, zero_mul, tsub_zero],
  ring,
end

-- @[simp]
lemma im_of_coe :
  (a:ℂ).im = a.y * rt_3/2 :=
begin
  change (to_ℂ a).im = a.y * rt_3/2,
  unfold to_ℂ,
  unfold complex_ω,
  simp only [add_im, int_cast_im, mul_im, int_cast_re, zero_mul, add_zero, zero_add],
  ring,
end

-- @[simp]
lemma y_from_coe :
  (a.y : ℝ) = 2*rt_3⁻¹ * (a:ℂ).im :=
begin
  cases a with x y,
  simp only [coe_of_mk],
  ring_nf,
  rw mul_comm,
  rw ← _root_.mul_assoc, 
  simp only [sqrt_3_inv_mul_self, _root_.one_mul, int.cast_inj, eq_self_iff_true],
end

-- @[simp]
lemma x_from_coe :
  (a.x :ℝ) = (a:ℂ).re + rt_3⁻¹ * (a:ℂ).im:=
begin
  cases a with x y,
  simp only [coe_of_mk],
  ring_nf,
  rw _root_.mul_assoc,
  rw mul_comm rt_3,
  simp only [one_div, sqrt_3_inv_mul_self, _root_.mul_one,
    sub_self, _root_.zero_mul, _root_.add_zero, int.cast_inj, eq_self_iff_true],
end


-- @[simp]
lemma coe_eq_zero { z : ℤω} :
  (z:ℂ)=0 ↔ z=0 :=
begin
  split,
  {
    intro h,
    ext,
    {
      have : (z.x : ℝ) = 0,
      rw [x_from_coe,h],
      norm_num,
      exact_mod_cast this,
    },
    {
      have : (z.y : ℝ) = 0,
      rw [y_from_coe,h],
      norm_num,
      exact_mod_cast this,
    },
  },
  {
    intro h,
    rw h,
    exact my_map_zero,
  }
end



#check map_add


-- @[simp]
lemma coe_neg : ((-a:ℤω):ℂ) = - (a:ℂ) :=
begin
  change to_ℂ (neg a) = - to_ℂ a,
  simp only [neg,to_ℂ],
  dsimp,
  norm_num,
  ring,
end 


-- @[simp]
lemma coe_sub :
  ((a - b:ℤω):ℂ) = (a:ℂ ) - (b: ℂ):=
begin
  change ((a +(-b):ℤω):ℂ)  = a + - (b:ℂ),
  rw  ← coe_neg,
  exact my_map_add a (-b),
end

-- @[simp]
lemma coe_mul :
  ((a*b:ℤω):ℂ) = (a:ℂ) * (b:ℂ) := my_map_mul _ _



/--
This is the `ℤ`-valued norm of an Eisenstein integer. 
-/
def Norm : ℤω → ℤ :=
  λ z, z.x^2 - z.x * z.y  + z.y^2


lemma norm_sq_coe :
  norm_sq a = (Norm a : ℤ)  :=
begin
  cases a with x y,
  simp [norm_sq,Norm],
  ring_nf,
  simp only [re_of_coe,im_of_coe],
  -- simp only [mul_inv_cancel, ne.def, bit0_eq_zero, one_ne_zero,
    -- not_false_iff, _root_.one_mul, rt_3_sq, inv_pow, add_right_inj],
  ring_nf,
  rw rt_3_sq,
  ring_nf,
end

def nat_Norm : ℤω → ℕ :=
  λ z, nat_abs (Norm z)

lemma nat_Norm_coe :
  norm_sq (a:ℂ) = (nat_Norm a :ℝ):=
begin
  unfold nat_Norm,
  rw norm_sq_coe,
  suffices : a.Norm = a.Norm.nat_abs,
  congr,
  exact this,
  refine eq_nat_abs_of_zero_le _,
  suffices : 0 ≤ norm_sq a,
  rewrite norm_sq_coe at this,
  exact_mod_cast this,
  exact norm_sq_nonneg _,
end

lemma Norm_mul :
  Norm (a*b) = Norm a * Norm b :=
begin
  have := norm_sq_mul a b,
  rw ← coe_mul at this,
  simp only [norm_sq_coe] at this,
  exact_mod_cast this,
end

lemma nat_Norm_mul :
  nat_Norm (a*b) = nat_Norm a * nat_Norm b :=
begin
  have := norm_sq_mul a b,
  rw ← coe_mul at this,
  simp only [nat_Norm_coe] at this,
  exact_mod_cast this,
end

lemma nat_Norm_eq_zero_iff :
  nat_Norm a = 0 ↔ a = 0 :=
begin
  split,
  {
    intro h,
    have : (a.nat_Norm : ℝ ) = 0,
    {
      exact_mod_cast h,
    },
    rw ← nat_Norm_coe at this,
    rw norm_sq_eq_zero at this,
    rwa coe_eq_zero at this,
  },
  {
    intro h,
    rw h,
    dec_trivial,
  }
end

noncomputable
def nearest_ℤω ( z : ℂ ) :  ℤω :=
  let y := round ( 2*rt_3⁻¹ * z.im) in
  {
    y := y,
    x := round (z.re + 2⁻¹ * y)
  }


/--
NOTE. This was working earlier by nlinarith, but for some reason the
automation no longer works. That's why I've used the complicated simp.
-/
lemma self_sub_round_sq ( x : ℝ ) :
  (x-round x)^2 ≤ (2⁻¹)^2  :=
begin
  rw sq_le_sq,
  have bound:= abs_sub_round x,
  have :|(2⁻¹:ℝ)| = 1/2 := by
    simp only [one_div, abs_eq_self, inv_nonneg,
               zero_le_bit0, zero_le_one],
  rwa this,
end

/--
We will use this in the case `c = √3/2`. 
-/
lemma sub_mul_round { c : ℝ } ( x : ℝ) (c_pos : c>0) :
  |x - c * round (c⁻¹ * x)| ≤  2⁻¹ * c :=
begin
  have hc : c* c⁻¹ = 1,
  {
    apply mul_inv_cancel,
    exact ne_of_gt c_pos,
  },
  have h_abs_c : |c| = c := abs_of_pos c_pos,
  have := abs_mul (c⁻¹ * x - round ( c⁻¹ * x )) c,
  rw sub_mul at this,
  rw mul_comm at this,
  rw ← mul_assoc at this,
  rw [hc,one_mul,mul_comm] at this,
  rw this, clear this,
  have := abs_sub_round (c⁻¹ * x),
  rw h_abs_c,
  rw mul_le_mul_right c_pos,
  rwa one_div at this,
end



lemma im_sub_nearest ( z : ℂ ) :
  (z-nearest_ℤω z).im^2 ≤ (4⁻¹ * rt_3)^2 :=
begin
  rw sq_le_sq,
  cases z with x y,
  unfold nearest_ℤω,
  dsimp,
  simp only [coe_of_mk], clear x,
  have := sub_mul_round y (_ : 2⁻¹ *rt_3 > 0),
  rw mul_comm at this,
  have arith :2⁻¹ * (2⁻¹* rt_3 ) = | 4⁻¹ * rt_3 |,
  {
    ring_nf,
    symmetry,
    simp only [one_div, abs_eq_self, zero_le_mul_right,
               real.sqrt_pos, zero_lt_three, inv_nonneg,
               zero_le_bit0, zero_le_one],
  },
  rwa arith at this, clear arith,
  ring_nf at this ⊢,
  have arith : (1/2 * rt_3)⁻¹ = 2 * rt_3⁻¹,
  {
    simp only [mul_comm, one_div, mul_inv_rev, inv_inv],
  },
  rwa arith at this,
  {
    simp only [gt_iff_lt, zero_lt_mul_right,
               real.sqrt_pos, zero_lt_three,
               inv_pos, zero_lt_bit0, zero_lt_one],
  }
end

lemma re_sub_nearest ( z : ℂ ) :
  (z-nearest_ℤω z).re^2 ≤  (2⁻¹)^2 :=
begin
  rw sq_le_sq,
  cases z with x y,
  unfold nearest_ℤω,
  dsimp,
  simp only [coe_of_mk],
  ring_nf,
  rw add_sub,
  have : | (1/2 : ℝ) | = 1/2 :=
    by simp only [one_div, abs_eq_self, inv_nonneg,
                  zero_le_bit0, zero_le_one],
  rw this,
  exact abs_sub_round _,
end




lemma norm_sub_nearest_ℤω_self_lt (z:ℂ) :
  norm_sq ( z - nearest_ℤω z ) < 1 :=
begin
  have hre := re_sub_nearest z,
  have him := im_sub_nearest z,
  unfold norm_sq,
  dsimp,
  simp only [← pow_two], 
  have arith : (2:ℝ)⁻¹ ^ 2 + (4⁻¹ * rt_3)^2 < 1,
  {
    ring_nf,
    simp only [one_div, rt_3_sq],
    norm_num,
  },
  have near := add_le_add hre him,
  have := lt_of_le_of_lt near arith,
  clear near arith hre him,
  rwa [sub_re,sub_im] at this,
end

noncomputable
def div : ℤω → ℤω → ℤω :=
  λ a b, nearest_ℤω (a/b)

noncomputable
def mod : ℤω → ℤω → ℤω :=
  λ a b, a - b * (div a b)

noncomputable
instance has_mod_ℤω : has_mod ℤω :=
{ mod := mod }

noncomputable
instance has_div_ℤω : has_div ℤω := { div := div }


theorem div_add_mod :
  b *(a/b) + (a%b) = a :=
begin
  change b * div a b + mod a b = a,
  simp [mod],
end

theorem norm_sq_mod_lt (h : b ≠ 0) :
  nat_Norm (mod a b) < nat_Norm b :=
begin
  suffices : complex.norm_sq (mod a b) < norm_sq b,
  {
    simp only [nat_Norm_coe] at this,
    exact_mod_cast this,
  },
  simp [mod,div],
  have bound : complex.norm_sq ( a/b - nearest_ℤω (a/b) ) < 1 :=
    norm_sub_nearest_ℤω_self_lt (a/b:ℂ),
  have : ((a/b:ℂ) - nearest_ℤω (a/b)) = (a - nearest_ℤω (a/b)*b)*b⁻¹,
  {
    ring_nf,
    have : (b:ℂ)* (b:ℂ)⁻¹ = 1,
    {
      apply mul_inv_cancel,
      simpa [coe_eq_zero] using h,
    },
    congr,
    rw mul_comm (b:ℂ),
    rw _root_.mul_assoc,
    rw this,
    rw _root_.mul_one,
  },
  rw this at bound, clear this,
  rw norm_sq_mul at bound,
  rw norm_sq_inv at bound,
  have bound2 : 0 < (complex.norm_sq b),
  {
    rw norm_sq_pos,
    intro h',
    rw coe_eq_zero at h',
    contradiction,
  },
  rw mul_inv_lt_iff bound2 at bound,
  rw mul_one at bound,
  rw mul_comm at bound,
  rw coe_sub,
  rw coe_mul,
  assumption,
end

lemma my_quotient_zero : div a 0 = 0 :=
begin
  unfold div,
  have : ((0:ℤω):ℂ)=0:= my_map_zero,
  rw [this,div_zero],
  unfold nearest_ℤω,
  ext;
  dsimp;
  simp only [mul_zero, round_zero, algebra_map.coe_zero, add_zero];
  refl,
end

lemma my_mul_left_not_lt (hb : b ≠ 0) :
  ¬ (nat_Norm (a*b) < nat_Norm a) :=
begin
  rw nat_Norm_mul,
  intro h,
  apply hb, clear hb,
  rw ← nat_Norm_eq_zero_iff,
  cases b.nat_Norm,
  { refl },
  {
    exfalso,
    rw nat.mul_succ at h,
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using h,
  }
end


noncomputable
instance euclidean_ℤω : euclidean_domain ℤω :=
{ add := add,
  zero := ⟨0,0⟩,
  zero_add := zero_add,
  add_zero := add_zero,
  add_assoc := add_assoc,
  neg := neg,
  add_left_neg := add_left_neg,
  add_comm := add_comm,
  one := ⟨1,0⟩,
  mul := mul,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  mul_comm := mul_comm,
  exists_pair_ne := begin
    use 0,
    use 1,
    dec_trivial,
  end,
  quotient := div,
  quotient_zero := my_quotient_zero,
  remainder := mod,
  quotient_mul_add_remainder_eq := div_add_mod,
  r := λ a b, nat_Norm a < nat_Norm b,
  r_well_founded := begin
    refine inv_image.wf (λ (a₁ : ℤω), nat_Norm a₁) _,
    exact { apply := _ },
    exact well_founded_lt.apply,
  end,
  remainder_lt := λ a b, by simpa using norm_sq_mod_lt a b,
  mul_left_not_lt := my_mul_left_not_lt
}


open euclidean_domain


/- Here is Bezout's theorem for ℤω. -/
#check euclidean_domain.gcd_eq_gcd_ab a b

/- Alternatively, we can prove it ourselves. -/
theorem Bezout (a b : ℤω) :
  ∃ h k : ℤω , h*a + k*b = gcd a b :=
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


end ℤω
