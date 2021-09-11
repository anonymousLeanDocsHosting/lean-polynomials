import field_definition
import field_results

def two (f : Type) [myfld f] : f := (myfld.one .+ myfld.one)
def four (f : Type) [myfld f] : f := ((two f) .+ (two f))

/- We have to add an additional stipulation that our fields are not of characteristic 2.-/ 
/- The quadratic formula is not defined for fields where 1 + 1 = 0.-/ 
class fld_not_char_two (f : Type _) [myfld f] := 
(not_char_two : myfld.one .+ myfld.one ≠ (myfld.zero : f))

lemma two_ne_zero (f : Type) [myfld f] [fld_not_char_two f] : (two f) ≠ myfld.zero := 
begin 
  unfold two, exact fld_not_char_two.not_char_two, 
end 

lemma two_plus_two (f : Type) [myfld f] : (two f) .+ (two f) = (two f) .* (two f) := 
begin 
  unfold two, rw distrib_simp f _ _ _, rw myfld.mul_comm myfld.one _, rw <- myfld.mul_one (myfld.one .+ myfld.one), 
end 

lemma four_ne_zero (f : Type) [myfld f] [fld_not_char_two f] : (four f) ≠ myfld.zero := 
begin 
  unfold four, rw two_plus_two, exact mul_nonzero f (two f) (two f) (two_ne_zero f) (two_ne_zero f), 
end 

lemma add_two_halves (f : Type) [myfld f] [fld_not_char_two f] : 
          (myfld.reciprocal (two f) (two_ne_zero f)) .+ (myfld.reciprocal (two f) (two_ne_zero f)) = myfld.one := 
begin 
  unfold two, 
  have h1 : (two f) .* (myfld.reciprocal (two f) (two_ne_zero f)) = myfld.one, 
    exact myfld.mul_reciprocal (two f) (two_ne_zero f), 
  unfold two at h1, rw distrib_simp f _ _ _ at h1, 
  rw myfld.mul_comm (myfld.one) _ at h1, 
  rw <- myfld.mul_one (myfld.reciprocal (myfld.one .+ myfld.one) (fld_not_char_two.not_char_two)) at h1, 
  exact h1, 
end 

/- Now we can move on to the preliminary work for the cubic formula.-/ 

/- We have to add an additional stipulation that our fields are not of characteristic 3.-/ 
/- The cubic formula is not defined for fields where 1 + 1 + 1 = 0.-/ 
def three (f : Type) [myfld f] : f := myfld.one .+ (myfld.one .+ myfld.one)

class fld_not_char_three (f : Type _) [myfld f] := 
(not_char_three : (three f) ≠ (myfld.zero : f))

def six (f : Type) [myfld f] : f := (two f) .* (three f)

lemma six_ne_zero (f : Type) [myfld f] [fld_not_char_two f] [fld_not_char_three f] : (six f) ≠ myfld.zero := 
begin 
  unfold six, unfold two, exact mul_nonzero f (myfld.one .+ myfld.one) (three f)
                                             fld_not_char_two.not_char_two fld_not_char_three.not_char_three, 
end 

def nine (f : Type) [myfld f] : f := ((three f) .* (three f))

lemma nine_ne_zero (f : Type) [myfld f] [fld_not_char_three f] : (nine f) ≠ myfld.zero := 
begin 
  unfold nine, exact mul_nonzero f (three f) (three f) fld_not_char_three.not_char_three fld_not_char_three.not_char_three, 
end 

def twenty_seven (f : Type) [myfld f] : f := (three f) .* (nine f)

lemma twenty_seven_ne_zero (f : Type) [myfld f] [fld_not_char_three f] : (twenty_seven f) ≠ myfld.zero := 
begin 
  unfold twenty_seven, exact mul_nonzero f (three f) (nine f) fld_not_char_three.not_char_three (nine_ne_zero f), 
end 

lemma three_cubed (f : Type) [myfld f] : (cubed f (three f)) = (twenty_seven f) := 
begin 
  unfold cubed, unfold twenty_seven, unfold nine, 
end 

def nine_minus_one (f : Type) [myfld f] : (((three f) .* (three f)) .+ (.- myfld.one)) = 
                                          (cubed f (two f)) := 
begin 
  unfold three, unfold two, unfold cubed, simp, 
end 

def one_plus_three (f : Type) [myfld f] : myfld.one .+ (three f) = (two f) .* (two f) := 
begin 
  unfold two, unfold three, simp, 
end 

lemma two_x_div_two (f : Type) [myfld f] [fld_not_char_two f] (a : f) : 
  (myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (a .+ a) = a := 
begin 
  unfold two, 
  rw [myfld.mul_one a] {occs := occurrences.pos [1, 2]}, 
  rw <- distrib_simp_alt f a, rw myfld.mul_comm a, rw myfld.mul_assoc, rw myfld.mul_comm (myfld.reciprocal _ _) _, 
  rw myfld.mul_reciprocal, rw one_mul_simp, 
end 