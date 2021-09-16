/- A natural number is either zero or the successor of a natural number.-/
inductive mynat : Type
  | zero   : mynat
  | mysucc : mynat → mynat

open mynat

lemma succ_eq (a b : mynat) : (a = b) -> (mysucc a = mysucc b) :=
begin
  intros h, rw h,
end

def nat_one : mynat := (mysucc zero)

def myadd : mynat → mynat → mynat
| x zero       := x
| x (mysucc y) := mysucc (myadd x y)

lemma add_zero (n : mynat) : myadd n zero = n :=
begin
  unfold myadd,
end
lemma add_succ (n m : mynat) : myadd n (mysucc m) = mysucc (myadd n m) :=
begin
  unfold myadd,
end

lemma zero_add (n : mynat) : myadd zero n = n :=
begin
  induction n,
    rw add_zero,
    rw add_succ, rw n_ih,
end

lemma succ_add (n m : mynat) : myadd (mysucc n) m = mysucc (myadd n m) :=
begin
  induction m,
    repeat {rw add_zero},
    rw add_succ, rw m_ih, refl,
end

lemma add_assoc (a b c : mynat) : myadd (myadd a b) c = myadd a (myadd b c) :=
begin
  induction c,
    repeat {rw add_zero},
    repeat {rw add_succ}, rw c_ih,
end

lemma add_comm (a b : mynat) : myadd a b = myadd b a :=
begin
  induction a,
    rw add_zero, rw zero_add,
    rw add_succ, rw succ_add, rw a_ih,
end

lemma add_cancel_a (a b c : mynat) : myadd b a = myadd c a -> b = c :=
begin
    intros h,
    induction a,
      repeat {rw add_zero at h}, exact h,
      repeat {rw add_succ at h}, simp at h, exact a_ih h,
end

lemma add_cancel_a_rev (a b c : mynat) : myadd a b = myadd a c -> b = c :=
begin
  rw add_comm a b, rw add_comm a c, exact add_cancel_a a b c,
end

lemma add_cancel_b (a b c : mynat) : b = c -> myadd b a = myadd c a :=
begin
    intros h,
    induction a,
      repeat {rw add_zero}, exact h,
      repeat {rw add_succ}, simp, exact a_ih,
end

lemma add_comm_in_tree (a b c d : mynat) : (myadd (myadd a b) (myadd c d)) = (myadd (myadd a c) (myadd b d)) :=
begin
  rw add_assoc, rw <- add_assoc b c d, rw add_comm b c, rw add_assoc c b d, rw <- add_assoc,
end

lemma add_combine_eq (a b c d : mynat) : (a = b) -> ((c = d) ->
                                          (myadd a c = myadd b d)) :=
begin
  intros h1 h2,
  rw h1, rw h2,
end

def mymul : mynat → mynat → mynat
| x zero       := zero
| x (mysucc y) := myadd x (mymul x y)

lemma zero_mul (n : mynat) : mymul zero n = zero :=
begin
  induction n,
    unfold mymul,
    unfold mymul, rw n_ih, unfold myadd,
end

lemma mul_zero (n : mynat) : mymul n zero = zero :=
begin
  unfold mymul,
end

lemma one_mul_eq (n : mynat) : mymul (mysucc zero) n = n :=
begin
  induction n,
    unfold mymul,
    unfold mymul, rw succ_add, rw n_ih, rw zero_add,
end

lemma mul_one_eq (n : mynat) : mymul n (mysucc zero) = n :=
begin
  cases n,
    rw zero_mul,
    unfold mymul, rw add_zero,
end

lemma mul_succ (n m : mynat) : mymul (mysucc n) m = myadd (mymul n m) m :=
begin
  induction m,
    unfold mymul, unfold myadd,
    unfold mymul, rw m_ih, repeat {unfold myadd}, rw add_assoc, rw succ_add,
end

lemma succ_mul (n m : mynat) : mymul n (mysucc m) = myadd (mymul n m) n :=
begin
  unfold mymul, rw add_comm,
end

lemma mul_comm (n m : mynat) : mymul n m = mymul m n :=
begin
  induction n,
    rw zero_mul, unfold mymul,
    rw mul_succ, rw n_ih, unfold mymul, rw add_comm,
end

lemma mul_add (t a b : mynat) : (mymul t (myadd a b)) =
                      (myadd (mymul t a) (mymul t b)) :=
begin
  induction b,
    unfold mymul, unfold myadd,
    repeat {rw add_succ}, repeat {unfold mymul}, rw b_ih,
      rw add_comm (mymul t a), rw <- add_assoc, rw add_comm,
end

lemma mul_assoc (a b c : mynat) : mymul (mymul a b) c = mymul a (mymul b c) :=
begin
  induction c,
    unfold mymul,
    repeat {rw succ_mul}, rw mul_add, rw c_ih,
end

lemma mul_add_distrib (a b c : mynat) : mymul (myadd a b) c =
                                  myadd (mymul a c) (mymul b c) :=
begin
  induction c with c1,
    unfold mymul, unfold myadd,
    unfold mymul, rw c_ih,
    rw add_comm a b, rw add_assoc, rw add_comm, rw add_comm b (mymul b c1),
    repeat {rw add_assoc},
end

lemma mul_add_distrib_alt (a b c : mynat) : mymul a (myadd b c) = myadd (mymul a b) (mymul a c) :=
begin
  rw mul_comm, rw mul_add_distrib, rw mul_comm b a, rw mul_comm c a,
end

lemma mul_add_distrib_rev (a b c : mynat) : myadd (mymul a b) (mymul a c) = mymul (myadd b c) a :=
begin
  rw mul_comm, rw mul_comm a c, rw <- mul_add_distrib,
end

lemma mul_two (a : mynat) : mymul zero.mysucc.mysucc a = myadd a a :=
begin
  rw mul_comm, unfold mymul, rw add_zero,
end

lemma mul_result_zero (a b c : mynat) : (a = mysucc(c)) -> ((mymul a b = zero) -> (b = zero)) :=
begin
  intros h1 h2, rw h1 at h2, cases b,
    refl,
    unfold mymul at h2, rw add_comm at h2, unfold myadd at h2, contradiction,
end

lemma mul_cancel (a b c : mynat) : (mymul a (mysucc c) = mymul b (mysucc c)) -> (a = b) :=
begin
  rw mul_comm, rw mul_comm b c.mysucc, revert b,
  induction a with a1, intro b, cases b,
      intros, refl,
      intros h, repeat {unfold mymul at h}, rw add_comm at h, unfold myadd at h, contradiction,
    intro b, cases b,
      intros h, repeat {unfold mymul at h}, rw add_comm at h, unfold myadd at h, contradiction,
      intros h1, unfold mymul at h1,
      have h2 : (mymul c.mysucc a1) = (mymul c.mysucc b),
        exact add_cancel_a_rev c.mysucc (mymul c.mysucc a1) (mymul c.mysucc b) h1,
      apply succ_eq a1 b,
      exact a_ih b h2,
end

lemma mul_zero_collapse (a b c : mynat) : ¬(a = b) -> ((mymul a c = mymul b c) -> c = zero) :=
begin
  intros h1 h2, cases c,
    refl,
    have absurd : a = b,
      exact mul_cancel a b c h2,
    exfalso, exact h1 absurd,
end

lemma add_self_eq_mul_two (a : mynat) : (myadd a a) = (mymul (zero.mysucc.mysucc) a) :=
begin
  induction a with a1,
    unfold myadd, unfold mymul,
    unfold mymul, unfold myadd,  rw add_comm, unfold myadd,
      rw add_comm zero.mysucc.mysucc (mymul zero.mysucc.mysucc a1), repeat {unfold myadd}, rw a_ih,
end

lemma add_self (a b : mynat) : (myadd a a = myadd b b) -> (a = b) :=
begin
  repeat {rw add_self_eq_mul_two}, intros h,
  rw mul_comm zero.mysucc.mysucc a at h, rw mul_comm zero.mysucc.mysucc b at h,
  exact mul_cancel a b zero.mysucc h,
end

lemma add_self_inv (a b : mynat) : ¬(a = b) -> ¬(myadd a a = myadd b b) :=
begin
  intros h, intros h2, exact h (add_self a b h2),
end

lemma mul_weird_sub_a (a b c d : mynat) : (∃e : mynat, d = (myadd c (mysucc e))) ->
        (myadd (mymul a c) (mymul b d)) = (myadd (mymul b c) (mymul a d)) ->
        (a = b) :=
begin
  intros h1 h2, cases h1 with e h1, rw h1 at h2,
  rw mul_add_distrib_alt b c e.mysucc at h2, rw mul_add_distrib_alt a c e.mysucc at h2,
  rw <- add_assoc (mymul a c) (mymul b c) (mymul b e.mysucc) at h2, rw <- add_assoc (mymul b c) (mymul a c) (mymul a e.mysucc) at h2,
  rw add_comm (mymul a c) (mymul b c) at h2,
  have tmp : (mymul b e.mysucc) = (mymul a e.mysucc),
    exact add_cancel_a_rev (myadd (mymul b c) (mymul a c)) (mymul b e.mysucc) (mymul a e.mysucc) h2,
  symmetry, exact mul_cancel b a e tmp,
end

lemma difference_exists (a b : mynat) : (∃c : mynat, (myadd a c) = b) \/ (∃c : mynat, a = (myadd b c)) :=
begin
  induction a,
    left, existsi b, rw zero_add,
    cases a_ih with h h,
      cases h with c hc, cases c,
        rw add_zero at hc, rw hc, right, existsi (zero.mysucc), unfold myadd,
        left, existsi c, unfold myadd at hc, rw succ_add, exact hc,
      cases h with c hc, cases c,
        rw add_zero at hc, rw hc, right, existsi (zero.mysucc), unfold myadd,
        right, existsi c.mysucc.mysucc, rw hc, unfold myadd,
end

lemma ne_implies_nonzero_diff (a b : mynat) : (a ≠ b) ->
              ((∃c : mynat, b = (myadd a c.mysucc)) \/ (∃c : mynat, a = (myadd b c.mysucc))) :=
begin
  intro h,
  have diff_h : (∃d : mynat, (myadd a d) = b) \/ (∃d : mynat, a = (myadd b d)),
    exact difference_exists a b,
  cases diff_h,
    left, cases diff_h with d hd, cases d,
      rw add_zero at hd, exfalso, exact h hd,
      existsi d, symmetry, exact hd,
    right, cases diff_h with d hd, cases d,
      rw add_zero at hd, exfalso, exact h hd,
      existsi d, exact hd,
end

/- This is a weird formula but we need it later, OK...-/
lemma mul_weird_sub (a b c d : mynat) : (c ≠ d) ->
        (myadd (mymul a c) (mymul b d)) = (myadd (mymul b c) (mymul a d)) ->
        (a = b) :=
begin
  intros h1 h2, cases (ne_implies_nonzero_diff c d h1) with h3 h3,
    exact mul_weird_sub_a a b c d h3 h2,
    symmetry, rw add_comm (mymul a c) (mymul b d) at h2, rw add_comm (mymul b c) (mymul a d) at h2,
      exact mul_weird_sub_a b a d c h3 h2,
end

/- We represent integers as a pair of natural numbers, where (a, b) represents (a - b).-/
inductive myint : Type
| int  : mynat -> mynat -> myint

open myint

def int_zero : myint := (int zero zero)
def int_one : myint := (int nat_one zero)

def iszero : myint -> Prop
| (int a b) := (a = b)

/- Because of the implementation, we need a new version of equals.-/
/- e.g. (0, 0) = (1, 1) as both represent zero, even though they are representationally different.-/
def int_equal : myint -> myint -> Prop
| (int a b) (int c d) := ((myadd a d) = (myadd b c))

lemma int_zeros_eq (a b : myint) : (iszero a) -> (iszero b) -> (int_equal a b) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold iszero, unfold int_equal, intros h1 h2, rw h1, rw h2,
end

lemma int_zeros_only_eq (a b : myint) : (iszero a) -> ((int_equal a b) -> (iszero b)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold iszero, unfold int_equal, intros h1 h2,
  rw h1 at h2,
  rw add_comm aminus bminus at h2, rw add_comm aminus bplus at h2,
  apply add_cancel_a aminus bplus bminus, symmetry, exact h2,
end

lemma int_zeros_only_eq_rev (a b : myint) : (iszero a) -> ((int_equal b a) -> (iszero b)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold iszero, unfold int_equal, intros h1 h2,
  rw h1 at h2,
  apply add_cancel_a aminus bplus bminus, exact h2,
end

lemma int_equal_refl (a : myint) : (int_equal a a) :=
begin
  cases a with aplus aminus, unfold int_equal,
  rw add_comm,
end

lemma int_eq_comm (a b : myint) : (int_equal a b) -> (int_equal b a) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold int_equal,
    intros h, rw add_comm bplus aminus, rw add_comm bminus aplus, symmetry, exact h,
end

lemma int_eq_comm_double (a b : myint) : (int_equal a b) <-> (int_equal b a) :=
begin
  split,
    exact int_eq_comm a b,
    exact int_eq_comm b a,
end

lemma int_eq_trans (a b c : myint) : (int_equal a b) -> (int_equal b c) ->
                                          (int_equal a c) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_equal,
  intros h1 h2,
  have h3 : (myadd (myadd aplus bminus) (myadd bplus cminus) = myadd (myadd aminus bplus) (myadd bminus cplus)),
    exact add_combine_eq (myadd aplus bminus) (myadd aminus bplus) (myadd bplus cminus) (myadd bminus cplus) h1 h2,
    apply add_cancel_a (myadd bplus bminus) (myadd aplus cminus) (myadd aminus cplus),
    rw add_comm bplus bminus, rw add_comm_in_tree, rw add_comm cminus bplus,
    symmetry,
    rw add_comm bminus bplus, rw add_comm_in_tree, symmetry, rw add_comm cplus bminus,
    exact h3,
end

def int_add : myint -> myint -> myint
| (int a b) (int c d) := (int (myadd a c) (myadd b d))

lemma add_zero_int (a b : myint) : (iszero a) ->
        (int_equal b (int_add a b)) :=
begin
  intros h, cases a with aplus aminus, unfold iszero at h,
  cases b with bplus bminus, unfold int_add, unfold int_equal,
  rw h, rw <- add_assoc, rw add_comm,
  have h : myadd bplus aminus = myadd aminus bplus,
    rw add_comm,
  rw h,
end

lemma add_zero_int_alt (a b : myint) : (iszero a) -> (int_equal (int_add a b) b) :=
begin
  intros h, have int : int_equal b (int_add a b), exact add_zero_int a b h, exact int_eq_comm b (int_add a b) int,
end

lemma add_comm_int (a b : myint) : int_equal (int_add a b) (int_add b a) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold int_add, unfold int_equal,
  rw add_comm (myadd aplus bplus) (myadd bminus aminus),
  rw add_comm aminus bminus,
  rw add_comm aplus bplus,
end

lemma add_comm_int_rw (a b : myint) : (int_add a b) = (int_add b a) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_add,
  rw add_comm bplus aplus, rw add_comm bminus aminus,
end

lemma add_eq (a b c : myint) : int_equal b c <->
                                int_equal (int_add a b) (int_add a c) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  split,
    intros h,
    unfold int_equal at h,
    unfold int_add, unfold int_equal,
    rw add_assoc, rw add_comm aminus cminus, rw <- add_assoc bplus cminus aminus,
    rw h,
    rw add_assoc, rw add_comm cplus aminus, rw <- add_assoc, rw <- add_assoc,
    rw add_comm aplus bminus,  rw add_comm (myadd bminus aplus) aminus,
    repeat {rw add_assoc},

    intros h,
    unfold int_equal, unfold int_add at h, unfold int_equal at h,
    rw add_assoc at h, rw add_comm at h, rw add_comm aminus cminus at h,
    rw add_comm aplus cplus at h, rw add_comm aminus bminus at h,
    rw add_assoc bminus aminus (myadd cplus aplus) at h,
    rw <- add_assoc aminus cplus aplus at h,
    rw add_comm aminus cplus at h, rw add_assoc cplus aminus aplus at h,
    rw <- add_assoc bminus cplus (myadd aminus aplus) at h,
    rw add_assoc at h, rw add_assoc cminus aminus aplus at h,
    rw <- add_assoc bplus cminus (myadd aminus aplus) at h,
    exact add_cancel_a (myadd aminus aplus) (myadd bplus cminus) (myadd bminus cplus) h,
end

lemma add_assoc_int (a b c : myint) : int_equal (int_add (int_add a b) c)
                                                (int_add a (int_add b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_add, unfold int_equal,
  rw add_comm,
  repeat {rw add_assoc},
end

lemma add_assoc_int_rw (a b c : myint) : (int_add (int_add a b) c) = (int_add a (int_add b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_add, repeat {rw add_assoc},
end

lemma add_sub_int (a b c d : myint) : (int_equal a b) -> (int_equal (int_add a c) d) ->
                                                         (int_equal (int_add b c) d) :=
begin
  intros h1 h2,
  have h3 : int_equal a b <-> int_equal (int_add c a) (int_add c b),
    exact add_eq c a b,
  cases h3 with h3 _,
  have h4 : int_equal (int_add c a) (int_add c b), exact h3 h1,
  rw add_comm_int_rw c a at h4, rw add_comm_int_rw c b at h4,
  have h5 : int_equal d (int_add a c), exact int_eq_comm (int_add a c) d h2,
  apply int_eq_comm d (int_add b c),
  exact int_eq_trans d (int_add a c) (int_add b c) h5 h4,
end

lemma int_add_self_nonzero (a : myint) : ¬(iszero a) -> ¬(iszero (int_add a a)) :=
begin
  cases a with aplus aminus, unfold int_add, unfold iszero, intros h,
  exact add_self_inv aplus aminus h,
end

/- (a - b)(c - d) = (ac + bd) - (ad + bc)-/
def int_mul : myint -> myint -> myint
| (int a b) (int c d) := (int (myadd (mymul a c) (mymul b d))
                              (myadd (mymul a d) (mymul b c)))

lemma mul_comm_int (a b : myint) : int_equal (int_mul a b) (int_mul b a) :=
begin
  cases a with aplus aminus, cases b with bplus bminus,
  unfold int_mul, unfold int_equal,
  rw add_comm,
  rw add_comm (mymul bplus aminus) (mymul bminus aplus),
  rw mul_comm bminus aplus, rw mul_comm bplus aminus,
  rw mul_comm aplus bplus, rw mul_comm aminus bminus,
end

lemma mul_comm_int_rw (a b : myint) : (int_mul a b) = (int_mul b a) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_mul,
  rw mul_comm bplus aplus, rw mul_comm bminus aminus,
  rw add_comm (mymul bplus aminus) (mymul bminus aplus),
  rw mul_comm bminus aplus, rw mul_comm bplus aminus,
end

/- Trivial consequence of previous results but makes some of the rewriting easier.-/
lemma add_helper_1 (a b c : mynat) : myadd (myadd a b) c = myadd (myadd a c) b :=
begin
  rw add_assoc, rw add_comm b c, rw <- add_assoc,
end

/- ditto -/
lemma add_helper_2 (a b c d : mynat) : myadd a (myadd (myadd b c) d) = myadd b (myadd (myadd a c) d) :=
begin
  repeat {rw <- add_assoc}, rw add_comm a b,
end

/- unlike for addition this implication only goes one way.
    (a * b) = (a * c) -> b = c
    is WRONG if a = 0.  -/
lemma mul_eq (a b c : myint) : int_equal b c ->
                            int_equal (int_mul a b) (int_mul a c) :=
begin
  intros h,
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_equal at h, unfold int_mul, unfold int_equal,
  rw add_comm (mymul aplus bplus) (mymul aminus bminus),
  repeat {rw add_assoc},
  rw <- add_assoc (mymul aplus bplus) (mymul aplus cminus) (mymul aminus cplus),
  rw mul_comm aplus bplus, rw mul_comm aplus cminus,
  rw <- mul_add_distrib,
  rw h, rw mul_add_distrib,
  rw add_comm (mymul aplus cplus) (mymul aminus cminus),
  rw <- add_assoc (mymul aminus bplus) (mymul aminus cminus) (mymul aplus cplus),
  rw mul_comm aminus bplus, rw mul_comm aminus cminus,
  rw <- mul_add_distrib bplus cminus aminus,
  rw h, rw mul_add_distrib,
  rw add_helper_1 (mymul bminus aminus) (mymul cplus aminus) (mymul aplus cplus),
  rw add_helper_2,
  rw mul_comm bminus aplus, rw mul_comm aminus bminus, rw mul_comm cplus aplus, rw mul_comm aminus cplus,
end

lemma mul_eq_alt (a b c : myint) : int_equal b c ->
                                  int_equal (int_mul b a) (int_mul c a) :=
begin
  intros h,
  have int1 : int_equal (int_mul a b) (int_mul a c),
    exact mul_eq a b c h,
  have int2 : int_equal (int_mul a b) (int_mul b a),
    exact mul_comm_int a b,
  have int3 : int_equal (int_mul b a) (int_mul a c),
    exact int_eq_trans (int_mul b a) (int_mul a b) (int_mul a c) (int_eq_comm (int_mul a b) (int_mul b a) int2) int1,
  exact int_eq_trans (int_mul b a) (int_mul a c) (int_mul c a) int3 (mul_comm_int a c),
end

attribute [simp]
lemma mul_assoc_int (a b c : myint) : int_equal (int_mul (int_mul a b) c)
                                                (int_mul a (int_mul b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_mul, unfold int_equal,
  repeat {rw mul_add_distrib}, repeat {rw mul_add_distrib_alt},
  /- The below code was generated with an external python script.-/
  /- It is almost certainly not the most efficient way to do this, but it works...-/
  rw add_comm (mymul aminus (mymul bplus cplus)) (mymul aminus (mymul bminus cminus)), rw <- add_assoc (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))) (mymul aminus (mymul bminus cminus)) (mymul aminus (mymul bplus cplus)), rw add_comm (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))) (mymul aminus (mymul bminus cminus)), rw <- add_assoc (myadd (myadd (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus)) (myadd (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus))) (myadd (mymul aminus (mymul bminus cminus)) (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus)))) (mymul aminus (mymul bplus cplus)), rw <- add_assoc (myadd (myadd (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus)) (myadd (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus))) (mymul aminus (mymul bminus cminus)) (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))), rw add_comm (myadd (myadd (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus)) (myadd (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus))) (mymul aminus (mymul bminus cminus)), rw add_comm (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus), rw <- add_assoc (mymul aminus (mymul bminus cminus)) (myadd (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus)) (myadd (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus)), rw <- add_assoc (mymul aminus (mymul bminus cminus)) (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus), rw add_comm (mymul aminus (mymul bminus cminus)) (mymul (mymul aminus bminus) cplus), rw add_comm (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus), rw <- add_assoc (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus)) (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bminus) cminus), rw add_comm (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus)) (mymul (mymul aminus bplus) cminus), rw add_comm (myadd (myadd (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus))) (mymul (mymul aplus bminus) cminus)) (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus)))) (mymul aminus (mymul bplus cplus)), rw add_comm (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus))) (mymul (mymul aplus bminus) cminus), rw <- add_assoc (mymul aminus (mymul bplus cplus)) (myadd (mymul (mymul aplus bminus) cminus) (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus)))) (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))), rw <- add_assoc (mymul aminus (mymul bplus cplus)) (mymul (mymul aplus bminus) cminus) (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus))), rw add_comm (mymul aminus (mymul bplus cplus)) (mymul (mymul aplus bminus) cminus), rw add_comm (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus)), rw <- add_assoc (myadd (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus)))) (mymul aplus (mymul bminus cplus)) (mymul aplus (mymul bplus cminus)), rw add_comm (myadd (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus)))) (mymul aplus (mymul bminus cplus)), rw add_comm (myadd (mymul aplus (mymul bminus cplus)) (myadd (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (myadd (mymul (mymul aminus bplus) cminus) (myadd (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus))))) (mymul aplus (mymul bplus cminus)), rw add_comm (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bplus) cplus) (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))), rw add_comm (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (myadd (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bplus) cminus)) (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))), rw <- add_assoc (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bplus) cminus), rw add_comm (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (mymul aplus (mymul bminus cplus)) (myadd (myadd (mymul (mymul aplus bplus) cplus) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus)))) (mymul (mymul aminus bplus) cminus)) (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))), rw <- add_assoc (mymul aplus (mymul bminus cplus)) (myadd (mymul (mymul aplus bplus) cplus) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus)))) (mymul (mymul aminus bplus) cminus), rw <- add_assoc (mymul aplus (mymul bminus cplus)) (mymul (mymul aplus bplus) cplus) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))), rw add_comm (mymul aplus (mymul bminus cplus)) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (mymul aplus (mymul bplus cminus)) (myadd (myadd (myadd (mymul (mymul aplus bplus) cplus) (mymul aplus (mymul bminus cplus))) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus)))) (mymul (mymul aminus bplus) cminus)) (myadd (mymul (mymul aminus bminus) cplus) (mymul aminus (mymul bminus cminus))), rw <- add_assoc (mymul aplus (mymul bplus cminus)) (myadd (myadd (mymul (mymul aplus bplus) cplus) (mymul aplus (mymul bminus cplus))) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus)))) (mymul (mymul aminus bplus) cminus), rw <- add_assoc (mymul aplus (mymul bplus cminus)) (myadd (mymul (mymul aplus bplus) cplus) (mymul aplus (mymul bminus cplus))) (myadd (mymul (mymul aplus bminus) cminus) (mymul aminus (mymul bplus cplus))), rw <- add_assoc (mymul aplus (mymul bplus cminus)) (mymul (mymul aplus bplus) cplus) (mymul aplus (mymul bminus cplus)), rw add_comm (mymul aplus (mymul bplus cminus)) (mymul (mymul aplus bplus) cplus),
  symmetry,
  rw add_comm (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bminus) cminus), rw add_comm (mymul aminus (mymul bplus cminus)) (mymul aminus (mymul bminus cplus)), rw <- add_assoc (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))) (mymul aminus (mymul bminus cplus)) (mymul aminus (mymul bplus cminus)), rw add_comm (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))) (mymul aminus (mymul bminus cplus)), rw <- add_assoc (myadd (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (myadd (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus))) (myadd (mymul aminus (mymul bminus cplus)) (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus)))) (mymul aminus (mymul bplus cminus)), rw <- add_assoc (myadd (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (myadd (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus))) (mymul aminus (mymul bminus cplus)) (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))), rw add_comm (myadd (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (myadd (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus))) (mymul aminus (mymul bminus cplus)), rw add_comm (myadd (myadd (mymul aminus (mymul bminus cplus)) (myadd (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (myadd (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus)))) (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus)))) (mymul aminus (mymul bplus cminus)), rw add_comm (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus), rw <- add_assoc (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (mymul (mymul aminus bplus) cplus) (mymul (mymul aplus bminus) cplus), rw add_comm (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (mymul (mymul aminus bplus) cplus), rw <- add_assoc (mymul aminus (mymul bminus cplus)) (myadd (mymul (mymul aminus bplus) cplus) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus), rw <- add_assoc (mymul aminus (mymul bminus cplus)) (mymul (mymul aminus bplus) cplus) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)), rw add_comm (mymul aminus (mymul bminus cplus)) (mymul (mymul aminus bplus) cplus), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (myadd (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus)) (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bminus cplus)), rw add_comm (mymul aminus (mymul bplus cminus)) (mymul (mymul aminus bplus) cplus), rw add_comm (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus)), rw <- add_assoc (myadd (myadd (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus)) (mymul aplus (mymul bminus cminus)) (mymul aplus (mymul bplus cplus)), rw add_comm (myadd (myadd (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus)) (mymul aplus (mymul bminus cminus)), rw add_comm (myadd (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus), rw <- add_assoc (mymul aplus (mymul bminus cminus)) (mymul (mymul aplus bminus) cplus) (myadd (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))), rw add_comm (mymul aplus (mymul bminus cminus)) (mymul (mymul aplus bminus) cplus), rw add_comm (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus), rw <- add_assoc (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bminus) cminus), rw add_comm (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (mymul (mymul aplus bplus) cminus), rw <- add_assoc (myadd (mymul (mymul aplus bminus) cplus) (mymul aplus (mymul bminus cminus))) (myadd (mymul (mymul aplus bplus) cminus) (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus)))) (mymul (mymul aminus bminus) cminus), rw <- add_assoc (myadd (mymul (mymul aplus bminus) cplus) (mymul aplus (mymul bminus cminus))) (mymul (mymul aplus bplus) cminus) (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))), rw add_comm (myadd (mymul (mymul aplus bminus) cplus) (mymul aplus (mymul bminus cminus))) (mymul (mymul aplus bplus) cminus), rw add_comm (myadd (myadd (myadd (mymul (mymul aplus bplus) cminus) (myadd (mymul (mymul aplus bminus) cplus) (mymul aplus (mymul bminus cminus)))) (myadd (myadd (mymul (mymul aminus bplus) cplus) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus)))) (mymul (mymul aminus bminus) cminus)) (mymul aplus (mymul bplus cplus)),
  repeat {rw add_assoc},
  repeat {rw mul_assoc},
end

lemma mul_assoc_int_rw (a b c : myint) : (int_mul (int_mul a b) c) = (int_mul a (int_mul b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_mul, repeat {rw mul_add_distrib},
  /- Also python. -/
  rw add_comm (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus), rw add_comm (mymul (mymul aplus bminus) cminus) (mymul (mymul aminus bplus) cminus), rw <- add_assoc (myadd (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus)) (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bminus) cminus), rw add_comm (myadd (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus)) (mymul (mymul aminus bplus) cminus), rw add_comm (myadd (mymul (mymul aminus bplus) cminus) (myadd (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus))) (mymul (mymul aplus bminus) cminus), rw add_comm (mymul (mymul aminus bminus) cplus) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bminus) cplus), rw add_comm (mymul (mymul aminus bplus) cminus) (mymul (mymul aplus bplus) cplus), rw <- add_assoc (mymul (mymul aplus bminus) cminus) (myadd (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bplus) cminus)) (mymul (mymul aminus bminus) cplus), rw <- add_assoc (mymul (mymul aplus bminus) cminus) (mymul (mymul aplus bplus) cplus) (mymul (mymul aminus bplus) cminus), rw add_comm (mymul (mymul aplus bminus) cminus) (mymul (mymul aplus bplus) cplus),
  rw add_comm (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bminus) cminus), rw add_comm (mymul (mymul aplus bminus) cplus) (mymul (mymul aminus bplus) cplus), rw <- add_assoc (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (mymul (mymul aminus bplus) cplus) (mymul (mymul aplus bminus) cplus), rw add_comm (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus)) (mymul (mymul aminus bplus) cplus), rw add_comm (myadd (mymul (mymul aminus bplus) cplus) (myadd (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus))) (mymul (mymul aplus bminus) cplus), rw add_comm (mymul (mymul aminus bminus) cminus) (mymul (mymul aplus bplus) cminus), rw <- add_assoc (mymul (mymul aminus bplus) cplus) (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bminus) cminus), rw add_comm (mymul (mymul aminus bplus) cplus) (mymul (mymul aplus bplus) cminus), rw <- add_assoc (mymul (mymul aplus bminus) cplus) (myadd (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bplus) cplus)) (mymul (mymul aminus bminus) cminus), rw <- add_assoc (mymul (mymul aplus bminus) cplus) (mymul (mymul aplus bplus) cminus) (mymul (mymul aminus bplus) cplus), rw add_comm (mymul (mymul aplus bminus) cplus) (mymul (mymul aplus bplus) cminus),
  symmetry, repeat {rw mul_add_distrib_alt},
  rw add_comm (mymul aminus (mymul bplus cminus)) (mymul aminus (mymul bminus cplus)), rw <- add_assoc (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))) (mymul aminus (mymul bminus cplus)) (mymul aminus (mymul bplus cminus)), rw add_comm (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus))) (mymul aminus (mymul bminus cplus)), rw add_comm (myadd (mymul aminus (mymul bminus cplus)) (myadd (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus)))) (mymul aminus (mymul bplus cminus)), rw add_comm (mymul aplus (mymul bplus cplus)) (mymul aplus (mymul bminus cminus)), rw <- add_assoc (mymul aminus (mymul bminus cplus)) (mymul aplus (mymul bminus cminus)) (mymul aplus (mymul bplus cplus)), rw add_comm (mymul aminus (mymul bminus cplus)) (mymul aplus (mymul bminus cminus)), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (myadd (mymul aplus (mymul bminus cminus)) (mymul aminus (mymul bminus cplus))) (mymul aplus (mymul bplus cplus)), rw <- add_assoc (mymul aminus (mymul bplus cminus)) (mymul aplus (mymul bminus cminus)) (mymul aminus (mymul bminus cplus)), rw add_comm (mymul aminus (mymul bplus cminus)) (mymul aplus (mymul bminus cminus)), rw add_comm (myadd (myadd (mymul aplus (mymul bminus cminus)) (mymul aminus (mymul bplus cminus))) (mymul aminus (mymul bminus cplus))) (mymul aplus (mymul bplus cplus)),
  rw add_comm (mymul aminus (mymul bplus cplus)) (mymul aminus (mymul bminus cminus)), rw <- add_assoc (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))) (mymul aminus (mymul bminus cminus)) (mymul aminus (mymul bplus cplus)), rw add_comm (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus))) (mymul aminus (mymul bminus cminus)), rw add_comm (myadd (mymul aminus (mymul bminus cminus)) (myadd (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus)))) (mymul aminus (mymul bplus cplus)), rw add_comm (mymul aplus (mymul bplus cminus)) (mymul aplus (mymul bminus cplus)), rw <- add_assoc (mymul aminus (mymul bminus cminus)) (mymul aplus (mymul bminus cplus)) (mymul aplus (mymul bplus cminus)), rw add_comm (mymul aminus (mymul bminus cminus)) (mymul aplus (mymul bminus cplus)), rw <- add_assoc (mymul aminus (mymul bplus cplus)) (myadd (mymul aplus (mymul bminus cplus)) (mymul aminus (mymul bminus cminus))) (mymul aplus (mymul bplus cminus)), rw <- add_assoc (mymul aminus (mymul bplus cplus)) (mymul aplus (mymul bminus cplus)) (mymul aminus (mymul bminus cminus)), rw add_comm (mymul aminus (mymul bplus cplus)) (mymul aplus (mymul bminus cplus)), rw add_comm (myadd (myadd (mymul aplus (mymul bminus cplus)) (mymul aminus (mymul bplus cplus))) (mymul aminus (mymul bminus cminus))) (mymul aplus (mymul bplus cminus)),
  repeat {rw mul_assoc}, repeat {rw add_assoc},
end

/- This will be useful later.-/
lemma mul_tree_swap_int_rw (a b c d : myint) : (int_mul (int_mul a b) (int_mul c d)) =
                                               (int_mul (int_mul a c) (int_mul b d)) :=
begin
  rw mul_assoc_int_rw a b (int_mul c d),
  rw <- mul_assoc_int_rw b c d,
  rw mul_comm_int_rw b c,
  rw mul_assoc_int_rw c b d,
  rw <- mul_assoc_int_rw a c (int_mul b d),
end

lemma mul_distrib_int (a b c : myint) : int_equal (int_mul (int_add a b) c)
                                        (int_add (int_mul a c) (int_mul b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_mul, unfold int_add, unfold int_mul, unfold int_equal,
  repeat {rw mul_add_distrib},
  /- Ditto.  Rewriting these massive chunks of addition manually seems like a bad
     use of time, even though it might produce marginally better code in the end.-/
  rw <- add_assoc (myadd (mymul aplus cplus) (mymul bplus cplus)) (mymul aminus cminus) (mymul bminus cminus), rw add_comm (myadd (mymul aplus cplus) (mymul bplus cplus)) (mymul aminus cminus), rw add_comm (mymul aplus cminus) (mymul aminus cplus), rw <- add_assoc (myadd (myadd (mymul aminus cminus) (myadd (mymul aplus cplus) (mymul bplus cplus))) (mymul bminus cminus)) (myadd (mymul aminus cplus) (mymul aplus cminus)) (myadd (mymul bplus cminus) (mymul bminus cplus)), rw <- add_assoc (myadd (myadd (mymul aminus cminus) (myadd (mymul aplus cplus) (mymul bplus cplus))) (mymul bminus cminus)) (mymul aminus cplus) (mymul aplus cminus), rw add_comm (myadd (myadd (mymul aminus cminus) (myadd (mymul aplus cplus) (mymul bplus cplus))) (mymul bminus cminus)) (mymul aminus cplus), rw add_comm (myadd (mymul aminus cplus) (myadd (myadd (mymul aminus cminus) (myadd (mymul aplus cplus) (mymul bplus cplus))) (mymul bminus cminus))) (mymul aplus cminus), rw <- add_assoc (mymul aminus cminus) (mymul aplus cplus) (mymul bplus cplus), rw add_comm (mymul aminus cminus) (mymul aplus cplus), rw <- add_assoc (mymul aminus cplus) (myadd (myadd (mymul aplus cplus) (mymul aminus cminus)) (mymul bplus cplus)) (mymul bminus cminus), rw <- add_assoc (mymul aminus cplus) (myadd (mymul aplus cplus) (mymul aminus cminus)) (mymul bplus cplus), rw <- add_assoc (mymul aminus cplus) (mymul aplus cplus) (mymul aminus cminus), rw add_comm (mymul aminus cplus) (mymul aplus cplus), rw <- add_assoc (mymul aplus cminus) (myadd (myadd (myadd (mymul aplus cplus) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus)) (mymul bminus cminus), rw <- add_assoc (mymul aplus cminus) (myadd (myadd (mymul aplus cplus) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus), rw <- add_assoc (mymul aplus cminus) (myadd (mymul aplus cplus) (mymul aminus cplus)) (mymul aminus cminus), rw <- add_assoc (mymul aplus cminus) (mymul aplus cplus) (mymul aminus cplus), rw add_comm (mymul aplus cminus) (mymul aplus cplus), rw add_comm (myadd (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus)) (mymul bminus cminus), rw add_comm (mymul bplus cminus) (mymul bminus cplus), rw <- add_assoc (myadd (mymul bminus cminus) (myadd (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus))) (mymul bminus cplus) (mymul bplus cminus), rw add_comm (myadd (mymul bminus cminus) (myadd (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus))) (mymul bminus cplus), rw add_comm (myadd (mymul bminus cplus) (myadd (mymul bminus cminus) (myadd (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus)))) (mymul bplus cminus), rw add_comm (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)) (mymul bplus cplus), rw <- add_assoc (mymul bminus cminus) (mymul bplus cplus) (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)), rw add_comm (mymul bminus cminus) (mymul bplus cplus), rw <- add_assoc (mymul bminus cplus) (myadd (mymul bplus cplus) (mymul bminus cminus)) (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)), rw <- add_assoc (mymul bminus cplus) (mymul bplus cplus) (mymul bminus cminus), rw add_comm (mymul bminus cplus) (mymul bplus cplus), rw <- add_assoc (mymul bplus cminus) (myadd (myadd (mymul bplus cplus) (mymul bminus cplus)) (mymul bminus cminus)) (myadd (myadd (myadd (mymul aplus cplus) (mymul aplus cminus)) (mymul aminus cplus)) (mymul aminus cminus)), rw <- add_assoc (mymul bplus cminus) (myadd (mymul bplus cplus) (mymul bminus cplus)) (mymul bminus cminus), rw <- add_assoc (mymul bplus cminus) (mymul bplus cplus) (mymul bminus cplus), rw add_comm (mymul bplus cminus) (mymul bplus cplus),
  symmetry,
  rw add_comm (mymul aplus cplus) (mymul aminus cminus), rw <- add_assoc (myadd (myadd (mymul aplus cminus) (mymul bplus cminus)) (myadd (mymul aminus cplus) (mymul bminus cplus))) (myadd (mymul aminus cminus) (mymul aplus cplus)) (myadd (mymul bplus cplus) (mymul bminus cminus)), rw <- add_assoc (myadd (myadd (mymul aplus cminus) (mymul bplus cminus)) (myadd (mymul aminus cplus) (mymul bminus cplus))) (mymul aminus cminus) (mymul aplus cplus), rw add_comm (myadd (myadd (mymul aplus cminus) (mymul bplus cminus)) (myadd (mymul aminus cplus) (mymul bminus cplus))) (mymul aminus cminus), rw <- add_assoc (myadd (mymul aplus cminus) (mymul bplus cminus)) (mymul aminus cplus) (mymul bminus cplus), rw add_comm (myadd (mymul aplus cminus) (mymul bplus cminus)) (mymul aminus cplus), rw <- add_assoc (mymul aminus cminus) (myadd (mymul aminus cplus) (myadd (mymul aplus cminus) (mymul bplus cminus))) (mymul bminus cplus), rw <- add_assoc (mymul aminus cminus) (mymul aminus cplus) (myadd (mymul aplus cminus) (mymul bplus cminus)), rw add_comm (mymul aminus cminus) (mymul aminus cplus), rw <- add_assoc (myadd (mymul aminus cplus) (mymul aminus cminus)) (mymul aplus cminus) (mymul bplus cminus), rw add_comm (myadd (mymul aminus cplus) (mymul aminus cminus)) (mymul aplus cminus), rw add_comm (myadd (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)) (mymul bminus cplus)) (mymul aplus cplus), rw add_comm (mymul bplus cplus) (mymul bminus cminus), rw <- add_assoc (myadd (mymul aplus cplus) (myadd (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)) (mymul bminus cplus))) (mymul bminus cminus) (mymul bplus cplus), rw add_comm (myadd (mymul aplus cplus) (myadd (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)) (mymul bminus cplus))) (mymul bminus cminus), rw add_comm (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)) (mymul bminus cplus), rw <- add_assoc (mymul aplus cplus) (mymul bminus cplus) (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)), rw add_comm (mymul aplus cplus) (mymul bminus cplus), rw <- add_assoc (mymul bminus cminus) (myadd (mymul bminus cplus) (mymul aplus cplus)) (myadd (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus)), rw <- add_assoc (mymul bminus cminus) (mymul bminus cplus) (mymul aplus cplus), rw add_comm (mymul bminus cminus) (mymul bminus cplus), rw add_comm (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))) (mymul bplus cminus), rw <- add_assoc (myadd (myadd (mymul bminus cplus) (mymul bminus cminus)) (mymul aplus cplus)) (mymul bplus cminus) (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus))), rw add_comm (myadd (myadd (mymul bminus cplus) (mymul bminus cminus)) (mymul aplus cplus)) (mymul bplus cminus), rw add_comm (myadd (myadd (mymul bplus cminus) (myadd (myadd (mymul bminus cplus) (mymul bminus cminus)) (mymul aplus cplus))) (myadd (mymul aplus cminus) (myadd (mymul aminus cplus) (mymul aminus cminus)))) (mymul bplus cplus),
  repeat {rw add_assoc},
end

lemma mul_distrib_int_rw (a b c : myint) : (int_mul (int_add a b) c) =
                                        (int_add (int_mul a c) (int_mul b c)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold int_mul, unfold int_add, unfold int_mul,
  repeat {rw mul_add_distrib},
  rw add_comm_in_tree (mymul aplus cplus) (mymul bplus cplus) (mymul aminus cminus) (mymul bminus cminus),
  rw add_comm_in_tree (mymul aplus cminus) (mymul bplus cminus) (mymul aminus cplus) (mymul bminus cplus),
end

lemma mul_distrib_int_rw_alt (a b c : myint) : (int_mul a (int_add b c)) = (int_add (int_mul a b) (int_mul a c)) :=
begin
  rw mul_comm_int_rw, rw mul_distrib_int_rw, rw mul_comm_int_rw b a, rw mul_comm_int_rw c a,
end

lemma mul_zero_int (a b : myint) : (iszero a) -> (iszero (int_mul a b)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_mul, unfold iszero,
  intros h, rw h, rw add_comm,
end

lemma mul_zero_int_alt (a b : myint) : (iszero a) -> (iszero (int_mul b a)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_mul, unfold iszero,
  intros h, rw h,
end

lemma mul_zero_int_zero (a : myint) : int_equal (int_mul a int_zero) int_zero :=
begin
  cases a with aplus aminus, unfold int_zero, unfold int_mul, rw mul_zero, rw zero_add, rw mul_zero,
  exact int_equal_refl (int zero zero),
end

lemma mul_result_zero_int (a b : myint) : (¬iszero a) -> (iszero (int_mul a b)) -> (iszero b) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_mul, unfold iszero,
  intros h1 h2,
  rw mul_comm aplus bplus at h2,
  rw mul_comm aminus bminus at h2,
  rw mul_comm aplus bminus at h2,
  rw mul_comm aminus bplus at h2,
  exact mul_weird_sub bplus bminus aplus aminus h1 h2,
end

lemma mul_result_zero_int_rev (a b : myint) : (¬iszero b) -> (iszero (int_mul a b)) -> iszero a :=
begin
  intros h1 h2, rw mul_comm_int_rw at h2,
  exact mul_result_zero_int b a h1 h2,
end

lemma mul_one_int (a : myint) : int_equal a (int_mul a int_one) :=
begin
  cases a with aplus aminus, unfold int_one, unfold nat_one, unfold int_mul, unfold int_equal,
  repeat {rw mul_one_eq}, repeat {rw mul_zero},
  rw add_zero, rw zero_add, rw add_comm,
end

lemma mul_one_int_rw (a : myint) : (int_mul a int_one) = a :=
begin
  cases a with aplus aminus,
  unfold int_one, unfold nat_one, unfold int_mul, repeat {rw mul_zero}, rw add_zero, rw zero_add,
  repeat {rw mul_one_eq},
end

lemma mul_one_int_rw_alt (a : myint) : (int_mul (int zero.mysucc zero) a) = a :=
begin
  cases a with plus minus, unfold int_mul, repeat {rw zero_mul}, repeat {rw add_zero},
  repeat {rw one_mul_eq},
end

lemma mul_comm_zero_int (a b : myint) : (iszero (int_mul a b)) = (iszero (int_mul b a)) :=
begin
  have h1 : int_equal (int_mul a b) (int_mul b a),
    exact mul_comm_int a b,
  by_cases (iszero (int_mul a b)),
    have h2 : (iszero (int_mul b a)),
      exact int_zeros_only_eq (int_mul a b) (int_mul b a) h h1,
    cc,

    by_cases (iszero (int_mul b a)),
      have absurd : (iszero (int_mul a b)),
        exact int_zeros_only_eq (int_mul b a) (int_mul a b) h (mul_comm_int b a),
      contradiction,
      cc,
end

lemma mul_sub_int (a b c d : myint) : (int_equal a b) -> (int_equal (int_mul a c) d) ->
                                                         (int_equal (int_mul b c) d) :=
begin
  intros h1 h2,
  exact int_eq_trans (int_mul b c) (int_mul a c) d
      (int_eq_comm (int_mul a c) (int_mul b c) (mul_eq_alt c a b h1)) h2,
end

lemma multiply_two_equalities_int (a b c d : myint) : int_equal a b -> int_equal c d ->
                                        (int_equal (int_mul a c) (int_mul b d)) :=
begin
  intros h1 h2,
  have tmp1 : int_equal (int_mul b d) (int_mul b d),
    exact int_equal_refl (int_mul b d),
  have tmp2 : int_equal (int_mul a d) (int_mul b d),
    exact mul_sub_int b a d (int_mul b d) (int_eq_comm a b h1) tmp1,
  have tmp3 : int_equal (int_mul a d) (int_mul d a),
    exact mul_comm_int a d,
  have tmp4 : int_equal (int_mul d a) (int_mul a c),
    exact mul_sub_int c d a (int_mul a c) h2 (mul_comm_int c a),
  exact int_eq_trans (int_mul a c) (int_mul a d) (int_mul b d)
    (int_eq_comm (int_mul a d) (int_mul a c)
      (int_eq_trans (int_mul a d) (int_mul d a) (int_mul a c) (mul_comm_int a d) tmp4)) tmp2,
end

lemma stupid (a b : mynat) : (a = b) = (b = a) :=
begin
  by_cases (a = b),
    cc,
    cc,
end

lemma mul_cancel_int (a b c : myint) : (¬ iszero b) -> (int_equal (int_mul a b) (int_mul c b)) ->
                                                       (int_equal a c) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, cases c with cplus cminus,
  unfold iszero, unfold int_mul, unfold int_equal, intros b_not_zero, intros h,

  /- Two python-generated lines.-/
  rw add_comm (mymul aplus bplus) (mymul aminus bminus) at h, rw <- add_assoc (myadd (mymul aminus bminus) (mymul aplus bplus)) (mymul cplus bminus) (mymul cminus bplus) at h, rw add_comm (myadd (mymul aminus bminus) (mymul aplus bplus)) (mymul cplus bminus) at h, rw add_comm (mymul aminus bminus) (mymul aplus bplus) at h, rw <- add_assoc (mymul cplus bminus) (mymul aplus bplus) (mymul aminus bminus) at h, rw add_comm (mymul cplus bminus) (mymul aplus bplus) at h, rw add_comm (myadd (myadd (mymul aplus bplus) (mymul cplus bminus)) (mymul aminus bminus)) (mymul cminus bplus) at h,
  rw stupid at h,
  rw add_comm (mymul cplus bplus) (mymul cminus bminus) at h, rw <- add_assoc (myadd (mymul aplus bminus) (mymul aminus bplus)) (mymul cminus bminus) (mymul cplus bplus) at h, rw add_comm (myadd (mymul aplus bminus) (mymul aminus bplus)) (mymul cminus bminus) at h, rw add_comm (mymul aplus bminus) (mymul aminus bplus) at h, rw <- add_assoc (mymul cminus bminus) (mymul aminus bplus) (mymul aplus bminus) at h, rw add_comm (mymul cminus bminus) (mymul aminus bplus) at h, rw add_comm (myadd (myadd (mymul aminus bplus) (mymul cminus bminus)) (mymul aplus bminus)) (mymul cplus bplus) at h,
  repeat {rw add_assoc at h},

  rw <- add_assoc (mymul cplus bplus) (mymul aminus bplus) (myadd (mymul cminus bminus) (mymul aplus bminus)) at h,
  rw <- mul_add_distrib cplus aminus bplus at h, rw <- mul_add_distrib cminus aplus bminus at h,
  rw <- add_assoc (mymul cminus bplus) (mymul aplus bplus) (myadd (mymul cplus bminus) (mymul aminus bminus)) at h,
  rw <- mul_add_distrib cminus aplus bplus at h, rw <- mul_add_distrib cplus aminus bminus at h,

  have tmp : (myadd cplus aminus) = (myadd cminus aplus),
    exact mul_weird_sub (myadd cplus aminus) (myadd cminus aplus) bplus bminus b_not_zero h,
  symmetry, rw add_comm aminus cplus, rw add_comm aplus cminus, exact tmp,
end

lemma mul_cancel_int_alt (a b c : myint) : (¬ iszero a) -> (int_equal (int_mul a b) (int_mul a c)) ->
                                                           (int_equal b c) :=
begin
  rw mul_comm_int_rw a b, rw mul_comm_int_rw a c, exact mul_cancel_int b a c,
end

lemma mul_nonzero_int (a b : myint) : (¬ iszero a) -> (¬ iszero b) -> (¬ iszero (int_mul a b)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold int_mul, unfold iszero, intros h1 h2,
  by_contradiction h,
  rw add_comm (mymul aplus bminus) (mymul aminus bplus) at h,
  exact h1 ((mul_weird_sub aplus aminus bplus bminus h2) h),
end

lemma mul_sub_in_add_int (a b c d e : myint) : (int_equal a b) -> (int_equal (int_add (int_mul a c) d) e) ->
                                                                  (int_equal (int_add (int_mul b c) d) e) :=
begin
  intros h1 h2,
  have h3 : int_equal (int_mul a c) (int_mul b c),
    exact mul_eq_alt c a b h1,
  exact add_sub_int (int_mul a c) (int_mul b c) d e h3 h2,
end

lemma mul_two_int (a : myint) : int_mul (int zero.mysucc.mysucc zero) a = (int_add a a) :=
begin
  cases a with plus minus, unfold int_add, unfold int_mul, repeat {rw zero_mul}, repeat {rw add_zero},
  repeat {rw mul_two},
end

def negative : myint -> myint
| (int pos neg) := (int neg pos)

def negative_eq (a b : myint) : (int_equal a b) -> (int_equal (negative a) (negative b)) :=
begin
  cases a with aplus aminus, cases b with bplus bminus, unfold negative, unfold int_equal, intros, cc,
end

def add_to_negative (a : myint) : (int_equal int_zero (int_add a (negative a))) :=
begin
  cases a with plus minus,
  unfold negative, unfold int_add, unfold int_zero, unfold int_equal, rw add_comm minus plus,
end

def add_to_negative_alt (a : myint) : iszero (int_add a (negative a)) :=
begin
  cases a with aplus aminus, unfold negative, unfold int_add, unfold iszero, rw add_comm aplus aminus,
end

def mul_negative (a b : myint) : int_mul a (negative b) = negative (int_mul a b) :=
begin
  cases a with apos aneg, cases b with bpos bneg, unfold negative, unfold int_mul, unfold negative,
end

def mul_negative_alt (a b : myint) : int_mul a (negative b) = int_mul (negative a) b :=
begin
  cases a with apos aneg, cases b with bpos bneg, unfold negative, unfold int_mul,
  rw add_comm (mymul apos bneg) (mymul aneg bpos),
  rw add_comm (mymul aneg bneg) (mymul apos bpos),
end

/- A rational number is a pair representing a/b -/
inductive myrat : Type
| rat : myint -> myint -> myrat

open myrat
/- Definition:
    A myrat where iszero (second component) is True is an undefined value
    All operations on myrat types should return an undefined value if given one.
    In this way, failure can propagate.
    Also, all predicates are True about undefined values, so that proofs
    do not have to start with "defined (a) ->".-/

def rat_zero : myrat := (rat int_zero int_one)

def rat_one : myrat := (rat int_one int_one)
def rat_two : myrat := (rat (int zero.mysucc.mysucc zero) int_one)

def defined : myrat -> Prop
| (rat _ den) := (¬(iszero den))

def iszero_rat : myrat -> Prop
| (rat num den) := (iszero num) \/ (iszero den)

lemma undef_iszero (a : myrat) : ¬(defined a) -> (iszero_rat a) :=
begin
  cases a with anum aden, unfold defined, unfold iszero_rat, intros, right, cc,
end

def rat_eq : myrat -> myrat -> Prop
| (rat anum aden) (rat bnum bden) := int_equal (int_mul anum bden) (int_mul aden bnum) \/
                                              (iszero aden) \/ (iszero bden)

lemma undef_eq (a b : myrat) : ¬(defined a) -> (rat_eq a b) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold defined, unfold rat_eq, intros,
  right, left, by_cases (¬(iszero aden)),
    cc, cc,
end

lemma rat_eq_refl (a : myrat) : (rat_eq a a) :=
begin
  cases a with anum aden, unfold rat_eq, left, exact mul_comm_int anum aden,
end

lemma rat_eq_comm (a b : myrat) : (rat_eq a b) -> (rat_eq b a) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_eq, intros h, cases h,
    left,
    have tmp1 : int_equal (int_mul bden anum) (int_mul anum bden),
      exact mul_comm_int bden anum,
    have tmp2 : int_equal (int_mul bden anum) (int_mul aden bnum),
      exact int_eq_trans (int_mul bden anum) (int_mul anum bden) (int_mul aden bnum) tmp1 h,
    have tmp3 : int_equal (int_mul aden bnum) (int_mul bnum aden),
      exact mul_comm_int aden bnum,
    exact int_eq_comm (int_mul bden anum) (int_mul bnum aden) (int_eq_trans (int_mul bden anum) (int_mul aden bnum) (int_mul bnum aden) tmp2 tmp3),

    cases h,
      right, right, exact h,
      right, left, exact h,
end

lemma eq_undef (a b : myrat) : ¬(defined b) -> (rat_eq a b) :=
begin
  intros h, exact rat_eq_comm b a (undef_eq b a h),
end

lemma zeroes_only_eq_rat (a b : myrat) : (defined a) -> (rat_eq a b) -> (iszero_rat a) -> (iszero_rat b) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_eq, unfold iszero_rat, unfold defined, intros h2 h3 h1,
  cases h1, cases h3,
    have tmp : iszero (int_mul aden bnum),
      exact int_zeros_only_eq (int_mul anum bden) (int_mul aden bnum) (mul_zero_int anum bden h1) h3,
    left, by_cases (iszero bnum), cc, exfalso, exact mul_nonzero_int aden bnum h2 h tmp,

    cases h3, cc, cc, cc,
end

lemma rat_eq_trans (a b c : myrat) : (defined b) -> (rat_eq a b) -> (rat_eq b c) -> (rat_eq a c) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, unfold rat_eq,
  intros h1, intros h2, intros h3,
  by_cases h4 : (iszero aden),
    right, left, exact h4,
  by_cases h5 : (iszero cden),
    right, right, exact h5,
  unfold defined at h1,
  cases h2, cases h3,
  by_cases (iszero bnum),

    have h6 : iszero (int_mul aden bnum),
      rw mul_comm_int_rw aden bnum,
      exact mul_zero_int bnum aden h,
    have h7 : iszero (int_mul bnum cden),
      exact mul_zero_int bnum cden h,
    have h8 : iszero anum,
      exact mul_result_zero_int_rev anum bden h1 (int_zeros_only_eq_rev (int_mul aden bnum) (int_mul anum bden) h6 h2),
    have h9 : iszero cnum,
      exact mul_result_zero_int bden cnum h1 (int_zeros_only_eq (int_mul bnum cden) (int_mul bden cnum) h7 h3),
    left,
    exact int_zeros_eq (int_mul anum cden) (int_mul aden cnum) (mul_zero_int anum cden h8) (mul_zero_int_alt cnum aden h9),

    have tmp : int_equal (int_mul (int_mul anum bden) (int_mul bnum cden)) (int_mul (int_mul aden bnum) (int_mul bden cnum)),
      exact multiply_two_equalities_int (int_mul anum bden) (int_mul aden bnum) (int_mul bnum cden) (int_mul bden cnum) h2 h3,
    rw mul_assoc_int_rw aden bnum (int_mul bden cnum) at tmp,
    rw <- mul_assoc_int_rw bnum bden cnum at tmp,
    rw mul_comm_int_rw (int_mul bnum bden) cnum at tmp,
    rw mul_assoc_int_rw anum bden (int_mul bnum cden) at tmp,
    rw <- mul_assoc_int_rw bden bnum cden at tmp,
    rw mul_comm_int_rw (int_mul bden bnum) cden at tmp,
    rw mul_comm_int_rw bden bnum at tmp,
    repeat {rw <- mul_assoc_int_rw at tmp},
    rw mul_assoc_int_rw (int_mul aden cnum) bnum bden at tmp,
    rw mul_assoc_int_rw (int_mul anum cden) bnum bden at tmp,
    have tmp2 : ¬ iszero (int_mul bnum bden),
      exact mul_nonzero_int bnum bden h h1,
    left, exact mul_cancel_int (int_mul anum cden) (int_mul bnum bden) (int_mul aden cnum) tmp2 tmp,

    cases h3, cc, cc, cases h2, cc, cc,
end

def rat_mul : myrat -> myrat -> myrat
| (rat anum aden) (rat bnum bden) := (rat (int_mul anum bnum) (int_mul aden bden))

lemma rat_mul_comm (a b : myrat) : (rat_mul a b) = (rat_mul b a) :=
begin
  cases a with anum aden, cases b with bnum bden,
  unfold rat_mul,
  rw mul_comm_int_rw anum bnum, rw mul_comm_int_rw aden bden,
end

lemma rat_mul_def (a b : myrat) : (defined a) -> (defined b) -> (defined (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden,
  unfold rat_mul, unfold defined, intros h1 h2,
  exact mul_nonzero_int aden bden h1 h2,
end

lemma rat_mul_undef (a b : myrat) : ¬(defined a) -> ¬(defined (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden,
  unfold rat_mul, unfold defined, intros,
  by_cases (iszero aden),
    have tmp : iszero (int_mul aden bden),
      exact mul_zero_int aden bden h,
    cc,
    cc,
end

lemma rat_undef_mul (a b : myrat) : ¬(defined b) -> ¬(defined (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden,
  unfold rat_mul, unfold defined, intros,
  by_cases (iszero bden),
    have tmp : iszero (int_mul aden bden),
      exact mul_zero_int_alt bden aden h,
    cc, cc,
end

lemma rat_mul_zero (a b : myrat) : (iszero_rat a) -> (iszero_rat (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_mul, unfold iszero_rat, intros h,
  cases h,
    left, exact mul_zero_int anum bnum h,
    right, exact mul_zero_int aden bden h,
end

lemma rat_mul_assoc (a b c : myrat) : (rat_mul (rat_mul a b) c) = (rat_mul a (rat_mul b c)) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden,
  unfold rat_mul,
  repeat {rw mul_assoc_int_rw},
end

lemma rat_mul_eq (a b c : myrat) : (rat_eq b c) -> (rat_eq (rat_mul a b) (rat_mul a c)) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden,
  unfold rat_mul, unfold rat_eq, intros h, cases h with h1 h1,
    left,
    have h2 : int_equal (int_mul (int_mul bnum cden) (int_mul anum aden)) (int_mul (int_mul bden cnum) (int_mul anum aden)),
      exact mul_eq_alt (int_mul anum aden) (int_mul bnum cden) (int_mul bden cnum) h1,
    rw mul_comm_int_rw anum bnum,
    rw mul_comm_int_rw aden cden,
    rw mul_tree_swap_int_rw bnum anum cden aden,
    rw mul_comm_int_rw aden bden,
    rw mul_comm_int_rw anum cnum,
    rw mul_tree_swap_int_rw bden aden cnum anum,
    rw mul_comm_int_rw aden anum, exact h2,

    right, cases h1,
      left, exact mul_zero_int_alt bden aden h1,
      right, exact mul_zero_int_alt cden aden h1,
end

lemma mul_sub_rat (a b c d : myrat) : (defined a) -> (rat_eq a b) ->
                                      (rat_eq (rat_mul a c) d) -> (rat_eq (rat_mul b c) d) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, cases d with dnum dden,
  unfold rat_mul, unfold rat_eq, intros h1 h2 h3,
  by_cases h6 : (iszero bden), right, left, exact mul_zero_int bden cden h6,
  by_cases h8 : (iszero cden), right, left, exact mul_zero_int_alt cden bden h8,
  cases h2 with h2,
    cases h3 with h3,
      unfold defined at h1,
    have h4 : int_equal (int_mul (int_mul bnum bden) (int_mul (int_mul anum cnum) dden))
                            (int_mul (int_mul bnum bden) (int_mul (int_mul aden cden) dnum)),
          exact mul_eq (int_mul bnum bden) (int_mul (int_mul anum cnum) dden) (int_mul (int_mul aden cden) dnum) h3,
        repeat {rw <- mul_assoc_int_rw at h4},
        rw mul_assoc_int_rw bnum bden anum at h4,
        rw mul_comm_int_rw bden anum at h4,
        rw mul_comm_int_rw bnum bden at h4,
        rw mul_assoc_int_rw bden bnum aden at h4,
        rw mul_comm_int_rw bnum aden at h4,
        by_cases h5 : (iszero bnum),
          have h7 : iszero anum,
            exact mul_result_zero_int_rev anum bden h6 (int_zeros_only_eq_rev (int_mul aden bnum) (int_mul anum bden) (mul_zero_int_alt bnum aden h5) h2),
          have h9 : iszero dnum,
            exact mul_result_zero_int (int_mul aden cden) dnum (mul_nonzero_int aden cden h1 h8) (int_zeros_only_eq (int_mul (int_mul anum cnum) dden) (int_mul (int_mul aden cden) dnum) (mul_zero_int (int_mul anum cnum) dden (mul_zero_int anum cnum h7)) h3),
          left,
          exact int_zeros_eq (int_mul (int_mul bnum cnum) dden) (int_mul (int_mul bden cden) dnum) (mul_zero_int (int_mul bnum cnum) dden (mul_zero_int bnum cnum h5)) (mul_zero_int_alt dnum (int_mul bden cden) h9),

          rw mul_comm_int_rw bden (int_mul aden bnum) at h4, rw mul_comm_int_rw bnum (int_mul anum bden) at h4,
          repeat {rw mul_assoc_int_rw at h4},
          rw <- mul_assoc_int_rw at h4,
          rw <- mul_assoc_int_rw aden bnum (int_mul bden (int_mul cden dnum)) at h4,
          have h7 : int_equal (int_mul (int_mul aden bnum) (int_mul bnum (int_mul cnum dden))) (int_mul (int_mul aden bnum) (int_mul bden (int_mul cden dnum))),
            exact mul_sub_int (int_mul anum bden) (int_mul aden bnum) (int_mul bnum (int_mul cnum dden)) (int_mul (int_mul aden bnum) (int_mul bden (int_mul cden dnum))) h2 h4,
          left, repeat {rw mul_assoc_int_rw},
          exact mul_cancel_int_alt (int_mul aden bnum) (int_mul bnum (int_mul cnum dden)) (int_mul bden (int_mul cden dnum)) (mul_nonzero_int aden bnum h1 h5) h7,

      cases h3 with h3,
        unfold defined at h1, right, left,
        have h7 : iszero cden,
          exact mul_result_zero_int aden cden h1 h3,
        contradiction,

        right, right, exact h3,

    cases h2,
      unfold defined at h1, contradiction,
      right, left, exact mul_zero_int bden cden h2,
end

lemma mul_eq_rat (a b c : myrat) : (rat_eq a b) -> (rat_eq (rat_mul a c) (rat_mul b c)) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, unfold rat_mul, unfold rat_eq,
  intros h1, cases h1 with h1,
    left, rw mul_tree_swap_int_rw anum cnum bden cden,
    have h2 : int_equal (int_mul aden bnum) (int_mul anum bden),
      exact int_eq_comm (int_mul anum bden) (int_mul aden bnum) h1,
    apply mul_sub_int (int_mul aden bnum) (int_mul anum bden) (int_mul cnum cden) (int_mul (int_mul aden cden) (int_mul bnum cnum)) h2,
    rw mul_comm_int_rw cnum cden, rw mul_tree_swap_int_rw aden bnum cden cnum,
    exact int_equal_refl (int_mul (int_mul aden cden) (int_mul bnum cnum)),

    cases h1 with h1,
      right, left, exact mul_zero_int aden cden h1,
      right, right, exact mul_zero_int bden cden h1,
end

lemma mul_eq_rat_alt (a b c : myrat) : (rat_eq a b) -> (rat_eq (rat_mul c a) (rat_mul c b)) :=
begin
  rw rat_mul_comm c a, rw rat_mul_comm c b, exact mul_eq_rat a b c,
end

def rat_add : myrat -> myrat -> myrat
| (rat anum aden) (rat bnum bden) := (rat (int_add (int_mul anum bden) (int_mul bnum aden))
                                                      (int_mul aden bden))

lemma rat_add_undef (a b : myrat) : ¬(defined a) -> ¬(defined (rat_add a b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_add, unfold defined, intros h1,
  by_cases h2 : (iszero aden),
    have h3 : iszero (int_mul aden bden),
      exact mul_zero_int aden bden h2,
    cc, cc,
end

lemma rat_add_def (a b : myrat) : (defined a) -> (defined b) -> (defined (rat_add a b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_add, unfold defined, intros h1 h2,
  exact mul_nonzero_int aden bden h1 h2,
end

lemma rat_add_zero (a b : myrat) : (iszero_rat a) -> (rat_eq (rat_add a b) b) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_add, unfold rat_eq, unfold iszero_rat, intros h,
  cases h, left,
  have h1 : (int_equal (int_mul bnum aden) (int_add (int_mul anum bden) (int_mul bnum aden))),
    exact add_zero_int (int_mul anum bden) (int_mul bnum aden) (mul_zero_int anum bden h),
  have h2 : int_equal (int_mul bden (int_mul bnum aden)) (int_mul bden (int_add (int_mul anum bden) (int_mul bnum aden))),
    exact mul_eq bden (int_mul bnum aden) (int_add (int_mul anum bden) (int_mul bnum aden)) h1,
  rw mul_comm_int_rw (int_add (int_mul anum bden) (int_mul bnum aden)) bden,
  rw mul_comm_int_rw aden bden, rw mul_assoc_int_rw bden aden bnum, rw mul_comm_int_rw aden bnum,
  exact int_eq_comm (int_mul bden (int_mul bnum aden)) (int_mul bden (int_add (int_mul anum bden) (int_mul bnum aden))) h2,

  right, left, exact mul_zero_int aden bden h,
end

lemma rat_add_zero_alt (a : myrat) : (rat_add a rat_zero) = a :=
begin
  unfold rat_zero, cases a with anum aden, unfold rat_add, repeat {rw mul_one_int_rw _},
  cases aden with adenplus adenminus, unfold int_zero, unfold int_mul,
  rw mul_comm, rw mul_comm zero adenminus, repeat {rw mul_zero}, unfold myadd,
  cases anum with anumplus anumminus, unfold int_add, repeat {rw add_zero},
end

lemma add_eq_rat (a b c : myrat) : (rat_eq a b) -> (rat_eq (rat_add a c) (rat_add b c)) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, unfold rat_add, unfold rat_eq, intros h,
  cases h, left,
    repeat {rw mul_distrib_int_rw}, repeat {rw mul_distrib_int_rw_alt},
    rw mul_assoc_int_rw anum cden (int_mul bden cden), rw <- mul_assoc_int_rw cden bden cden,
    rw mul_comm_int_rw cden bden, rw mul_assoc_int_rw bden cden cden,
    rw <- mul_assoc_int_rw anum bden (int_mul cden cden),
    apply mul_sub_in_add_int (int_mul aden bnum) (int_mul anum bden) (int_mul cden cden) (int_mul (int_mul cnum aden) (int_mul bden cden)) (int_add (int_mul (int_mul aden cden) (int_mul bnum cden)) (int_mul (int_mul aden cden) (int_mul cnum bden))) (int_eq_comm _ _ h),
    rw mul_assoc_int_rw aden bnum (int_mul cden cden), rw <- mul_assoc_int_rw bnum cden cden,
    rw mul_comm_int_rw bnum cden, rw mul_assoc_int_rw cden bnum cden,
    rw <- mul_assoc_int_rw aden cden (int_mul bnum cden), rw mul_comm_int_rw bnum cden,
    rw mul_comm_int_rw cnum aden, rw mul_comm_int_rw bden cden,
    rw mul_assoc_int_rw aden cnum (int_mul cden bden), rw <- mul_assoc_int_rw cnum cden bden,
    rw mul_comm_int_rw cnum cden, rw mul_assoc_int_rw cden cnum bden,
    rw <- mul_assoc_int_rw aden cden (int_mul cnum bden),
    exact int_equal_refl _,

    cases h,
      right, left,  exact mul_zero_int aden cden h,
      right, right, exact mul_zero_int bden cden h,
end

lemma rat_add_comm (a b : myrat) : (rat_add a b) = (rat_add b a) :=
begin
  cases a with anum aden, cases b with bnum bden,
  unfold rat_add,
  rw add_comm_int_rw (int_mul anum bden) (int_mul bnum aden),
  rw mul_comm_int_rw bden aden,
end

lemma rat_add_assoc (a b c : myrat) : (rat_add a (rat_add b c)) = (rat_add (rat_add a b) c) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, unfold rat_add,
  repeat {rw mul_assoc_int_rw}, repeat {rw mul_distrib_int_rw},
  repeat {rw mul_assoc_int_rw}, repeat {rw add_assoc_int_rw},
  rw mul_comm_int_rw aden bden, rw mul_comm_int_rw aden cden,
end

lemma add_sub_rat (a b c d : myrat) : (defined a) -> (rat_eq a b) ->
                                      (rat_eq (rat_add a c) d) -> (rat_eq (rat_add b c) d) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden, cases d with dnum dden,
  unfold rat_add, unfold rat_eq, intros h1 h2 h3, unfold defined at h1,
  by_cases h4 : iszero bden, right, left, exact mul_zero_int bden cden h4,
  by_cases h5 : iszero cden, right, left, exact mul_zero_int_alt cden bden h5,
  by_cases h6 : iszero dden, right, right, exact h6,
  left,
  cases h2 with h2, cases h3 with h3,
    by_cases h7 : (iszero anum),
      have h8 : (iszero bnum),
        exact mul_result_zero_int aden bnum h1 (int_zeros_only_eq (int_mul anum bden) (int_mul aden bnum) (mul_zero_int anum bden h7) h2),
      have h9 : int_equal (int_mul (int_mul cnum aden) dden) (int_mul (int_mul aden cden) dnum),
        exact mul_sub_int (int_add (int_mul anum cden) (int_mul cnum aden)) (int_mul cnum aden) dden (int_mul (int_mul aden cden) dnum) (add_zero_int_alt (int_mul anum cden) (int_mul cnum aden) (mul_zero_int anum cden h7)) h3,
      rw mul_comm_int_rw cnum aden at h9, repeat {rw mul_assoc_int_rw at h9},
      have h10 : int_equal (int_mul cnum dden) (int_mul cden dnum),
        exact mul_cancel_int_alt aden (int_mul cnum dden) (int_mul cden dnum) h1 h9,
      rw mul_distrib_int_rw,
      have h11 : int_equal (int_mul (int_mul cnum bden) dden) (int_add (int_mul (int_mul bnum cden) dden) (int_mul (int_mul cnum bden) dden)),
        exact add_zero_int (int_mul (int_mul bnum cden) dden) (int_mul (int_mul cnum bden) dden) (mul_zero_int (int_mul bnum cden) dden (mul_zero_int bnum cden h8)),
      rw mul_comm_int_rw cnum bden at h11, rw mul_assoc_int_rw bden cnum dden at h11, rw mul_comm_int_rw bden (int_mul cnum dden) at h11,
      have h12 : int_equal (int_mul (int_mul cden dnum) bden) (int_add (int_mul (int_mul bnum cden) dden) (int_mul (int_mul cnum dden) bden)),
        exact mul_sub_int (int_mul cnum dden) (int_mul cden dnum) bden (int_add (int_mul (int_mul bnum cden) dden) (int_mul (int_mul cnum dden) bden)) h10 h11,
      rw mul_assoc_int_rw cnum bden dden, rw mul_comm_int_rw bden dden, rw <- mul_assoc_int_rw cnum dden bden,
      rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden dnum, rw mul_comm_int_rw bden dnum, rw <- mul_assoc_int_rw cden dnum bden,
      exact int_eq_comm (int_mul (int_mul cden dnum) bden) (int_add (int_mul (int_mul bnum cden) dden) (int_mul (int_mul cnum dden) bden)) h12,

      rw mul_distrib_int_rw at h3, rw mul_distrib_int_rw,
      have h8 : int_equal (int_mul bden (int_add (int_mul (int_mul anum cden) dden) (int_mul (int_mul cnum aden) dden))) (int_mul bden (int_mul (int_mul aden cden) dnum)),
        exact mul_eq bden (int_add (int_mul (int_mul anum cden) dden) (int_mul (int_mul cnum aden) dden)) (int_mul (int_mul aden cden) dnum) h3,
      rw mul_distrib_int_rw_alt at h8,
      rw mul_assoc_int_rw anum cden dden at h8, rw <- mul_assoc_int_rw bden anum (int_mul cden dden) at h8, rw mul_comm_int_rw bden anum at h8,
      have h9 : int_equal (int_add (int_mul (int_mul aden bnum) (int_mul cden dden)) (int_mul bden (int_mul (int_mul cnum aden) dden))) (int_mul bden (int_mul (int_mul aden cden) dnum)),
        exact mul_sub_in_add_int (int_mul anum bden) (int_mul aden bnum) (int_mul cden dden) (int_mul bden (int_mul (int_mul cnum aden) dden)) (int_mul bden (int_mul (int_mul aden cden) dnum)) h2 h8,
      rw mul_assoc_int_rw aden bnum (int_mul cden dden) at h9,
      rw mul_comm_int_rw cnum aden at h9, rw mul_assoc_int_rw aden cnum dden at h9, rw <- mul_assoc_int_rw bden aden (int_mul cnum dden) at h9,
      rw mul_comm_int_rw bden aden at h9, rw mul_assoc_int_rw aden bden (int_mul cnum dden) at h9,
      rw <- mul_distrib_int_rw_alt aden (int_mul bnum (int_mul cden dden)) (int_mul bden (int_mul cnum dden)) at h9,
      rw mul_assoc_int_rw aden cden dnum at h9, rw <- mul_assoc_int_rw bden aden (int_mul cden dnum) at h9, rw mul_comm_int_rw bden aden at h9, rw mul_assoc_int_rw aden bden (int_mul cden dnum) at h9,
      rw mul_assoc_int_rw bnum cden dden, rw mul_assoc_int_rw bden cden dnum,
      rw mul_comm_int_rw cnum bden, rw mul_assoc_int_rw bden cnum dden,
      exact mul_cancel_int_alt aden (int_add (int_mul bnum (int_mul cden dden)) (int_mul bden (int_mul cnum dden))) (int_mul bden (int_mul cden dnum)) h1 h9,

    cases h3 with h3,
      exfalso, exact h5 (mul_result_zero_int aden cden h1 h3),
      contradiction,

    exfalso, cases h2 with h2, exact h1 h2, exact h4 h2,
end

lemma add_sub_rat_alt (a b c d : myrat) : (defined a) -> (rat_eq a b) -> (rat_eq (rat_add c a) d) -> (rat_eq (rat_add c b) d) :=
begin
  intros h1 h2 h3, rw rat_add_comm, rw rat_add_comm at h3, exact add_sub_rat a b c d h1 h2 h3,
end

lemma add_self_nonzero_rat (a : myrat) : ¬(iszero_rat a) -> ¬(iszero_rat (rat_add a a)) :=
begin
  cases a with anum aden, unfold rat_add, unfold iszero_rat, intros,
  by_cases (iszero (int_add (int_mul anum aden) (int_mul anum aden)) ∨ iszero (int_mul aden aden)),
  exfalso, cases h,
    by_cases h_anum : (iszero anum), cc,
    by_cases h_aden : (iszero aden), cc,
    exact int_add_self_nonzero (int_mul anum aden) (mul_nonzero_int anum aden h_anum h_aden) h,

    by_cases h_aden : (iszero aden), cc,
    exact (mul_nonzero_int aden aden h_aden h_aden) h,
    cc,
end

lemma rat_mul_zero_alt (a : myrat) : rat_eq rat_zero (rat_mul a rat_zero) :=
begin
  cases a with anum aden,
  unfold rat_zero, unfold int_zero, unfold int_one, unfold rat_mul, unfold rat_eq, by_cases (iszero aden),
    right, right, exact mul_zero_int aden (int nat_one zero) h,
    left, have int : iszero (int zero zero),
      unfold iszero,
    exact int_zeros_eq (int_mul (myint.int zero zero) (int_mul aden (myint.int nat_one zero))) ((int_mul (myint.int nat_one zero) (int_mul anum (myint.int zero zero)))) (mul_zero_int (myint.int zero zero) (int_mul aden (myint.int nat_one zero)) int) (mul_zero_int_alt (int_mul anum (myint.int zero zero)) ((myint.int nat_one zero)) (mul_zero_int_alt (myint.int zero zero) anum int)),
end

lemma rat_mul_one (a b : myrat) : rat_eq a rat_one -> rat_eq b (rat_mul a b) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_mul, unfold rat_one, unfold rat_eq, intros h, cases h,
    left, repeat {rw mul_one_int_rw at h},
    have h1 : int_equal aden anum,
      exact int_eq_comm anum aden h,
    rw <- mul_assoc_int_rw bnum aden bden, rw mul_comm_int_rw bnum aden, rw mul_assoc_int_rw aden bnum bden,
    rw <- mul_assoc_int_rw bden anum bnum, rw mul_comm_int_rw bden anum, rw mul_assoc_int_rw anum bden bnum,
    rw mul_comm_int_rw bnum bden,
    exact mul_eq_alt (int_mul bden bnum) aden anum h1,

    cases h,
      right, right, exact mul_zero_int aden bden h,
      unfold int_one at h, unfold iszero at h, unfold nat_one at h, cc,
end

lemma rat_mul_one_rw (a : myrat) : rat_mul a rat_one = a :=
begin
  cases a with num den, unfold rat_one, unfold rat_mul,
  cases num with numplus numminus, cases den with denplus denminus,
  unfold int_one, unfold int_mul, rw mul_zero, rw add_zero, unfold nat_one,
  rw mul_one_eq, rw mul_zero, rw zero_add, rw mul_one_eq, rw mul_one_eq, rw mul_zero, rw add_zero,
  rw mul_zero, rw zero_add, rw mul_one_eq,
end

lemma rat_mul_distrib (a b c : myrat) : rat_eq (rat_mul (rat_add a b) c) (rat_add (rat_mul a c) (rat_mul b c)) :=
begin
  cases a with anum aden, cases b with bnum bden, cases c with cnum cden,
  unfold rat_mul, unfold rat_add, unfold rat_mul,
  rw mul_distrib_int_rw, repeat {rw mul_assoc_int_rw},
  unfold rat_eq, left,
  rw mul_distrib_int_rw_alt, rw mul_distrib_int_rw, repeat {rw mul_assoc_int_rw},
  /- Don't lie and try to tell me you haven't missed the inefficient Python-generated code.-/
  rw <- mul_assoc_int_rw anum bden (int_mul cnum (int_mul aden (int_mul cden (int_mul bden cden)))), rw mul_comm_int_rw anum bden, rw mul_assoc_int_rw bden anum (int_mul cnum (int_mul aden (int_mul cden (int_mul bden cden)))), rw <- mul_assoc_int_rw anum cnum (int_mul aden (int_mul cden (int_mul bden cden))), rw mul_comm_int_rw anum cnum, rw mul_assoc_int_rw cnum anum (int_mul aden (int_mul cden (int_mul bden cden))), rw <- mul_assoc_int_rw aden cden (int_mul bden cden), rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden (int_mul bden cden), rw <- mul_assoc_int_rw aden bden cden, rw mul_comm_int_rw aden bden, rw mul_assoc_int_rw bden aden cden, rw mul_comm_int_rw aden cden, rw <- mul_assoc_int_rw bden cnum (int_mul anum (int_mul cden (int_mul bden (int_mul cden aden)))), rw mul_comm_int_rw bden cnum, rw mul_assoc_int_rw cnum bden (int_mul anum (int_mul cden (int_mul bden (int_mul cden aden)))), rw <- mul_assoc_int_rw anum cden (int_mul bden (int_mul cden aden)), rw mul_comm_int_rw anum cden, rw mul_assoc_int_rw cden anum (int_mul bden (int_mul cden aden)), rw <- mul_assoc_int_rw anum bden (int_mul cden aden), rw mul_comm_int_rw anum bden, rw mul_assoc_int_rw bden anum (int_mul cden aden), rw <- mul_assoc_int_rw anum cden aden, rw mul_comm_int_rw anum cden, rw mul_assoc_int_rw cden anum aden, rw <- mul_assoc_int_rw bden cden (int_mul bden (int_mul cden (int_mul anum aden))), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul bden (int_mul cden (int_mul anum aden))), rw <- mul_assoc_int_rw bden cden (int_mul anum aden), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul anum aden), rw <- mul_assoc_int_rw bden cden (int_mul bden (int_mul anum aden)), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul bden (int_mul anum aden)),
  rw <- mul_assoc_int_rw aden cnum (int_mul cden (int_mul bden (int_mul cden aden))), rw mul_comm_int_rw aden cnum, rw mul_assoc_int_rw cnum aden (int_mul cden (int_mul bden (int_mul cden aden))), rw <- mul_assoc_int_rw aden cden (int_mul bden (int_mul cden aden)), rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden (int_mul bden (int_mul cden aden)), rw <- mul_assoc_int_rw aden bden (int_mul cden aden), rw mul_comm_int_rw aden bden, rw mul_assoc_int_rw bden aden (int_mul cden aden), rw <- mul_assoc_int_rw aden cden aden, rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden aden, rw <- mul_assoc_int_rw bnum cnum (int_mul cden (int_mul bden (int_mul cden (int_mul aden aden)))), rw mul_comm_int_rw bnum cnum, rw mul_assoc_int_rw cnum bnum (int_mul cden (int_mul bden (int_mul cden (int_mul aden aden)))), rw <- mul_assoc_int_rw bnum cden (int_mul bden (int_mul cden (int_mul aden aden))), rw mul_comm_int_rw bnum cden, rw mul_assoc_int_rw cden bnum (int_mul bden (int_mul cden (int_mul aden aden))), rw <- mul_assoc_int_rw bden cden (int_mul aden aden), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul aden aden), rw <- mul_assoc_int_rw bnum cden (int_mul bden (int_mul aden aden)), rw mul_comm_int_rw bnum cden, rw mul_assoc_int_rw cden bnum (int_mul bden (int_mul aden aden)),
  apply int_eq_comm,
  rw <- mul_assoc_int_rw aden bden (int_mul cden (int_mul anum (int_mul cnum (int_mul cden bden)))), rw mul_comm_int_rw aden bden, rw mul_assoc_int_rw bden aden (int_mul cden (int_mul anum (int_mul cnum (int_mul cden bden)))), rw <- mul_assoc_int_rw aden cden (int_mul anum (int_mul cnum (int_mul cden bden))), rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden (int_mul anum (int_mul cnum (int_mul cden bden))), rw <- mul_assoc_int_rw aden anum (int_mul cnum (int_mul cden bden)), rw mul_comm_int_rw aden anum, rw mul_assoc_int_rw anum aden (int_mul cnum (int_mul cden bden)), rw <- mul_assoc_int_rw aden cnum (int_mul cden bden), rw mul_comm_int_rw aden cnum, rw mul_assoc_int_rw cnum aden (int_mul cden bden), rw <- mul_assoc_int_rw aden cden bden, rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden bden, rw mul_comm_int_rw aden bden, rw <- mul_assoc_int_rw bden cden (int_mul anum (int_mul cnum (int_mul cden (int_mul bden aden)))), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul anum (int_mul cnum (int_mul cden (int_mul bden aden)))), rw <- mul_assoc_int_rw anum cnum (int_mul cden (int_mul bden aden)), rw mul_comm_int_rw anum cnum, rw mul_assoc_int_rw cnum anum (int_mul cden (int_mul bden aden)), rw <- mul_assoc_int_rw anum cden (int_mul bden aden), rw mul_comm_int_rw anum cden, rw mul_assoc_int_rw cden anum (int_mul bden aden), rw <- mul_assoc_int_rw anum bden aden, rw mul_comm_int_rw anum bden, rw mul_assoc_int_rw bden anum aden, rw <- mul_assoc_int_rw bden cnum (int_mul cden (int_mul bden (int_mul anum aden))), rw mul_comm_int_rw bden cnum, rw mul_assoc_int_rw cnum bden (int_mul cden (int_mul bden (int_mul anum aden))), rw <- mul_assoc_int_rw bden cden (int_mul bden (int_mul anum aden)), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul bden (int_mul anum aden)), rw <- mul_assoc_int_rw cden cnum (int_mul cden (int_mul bden (int_mul bden (int_mul anum aden)))), rw mul_comm_int_rw cden cnum, rw mul_assoc_int_rw cnum cden (int_mul cden (int_mul bden (int_mul bden (int_mul anum aden)))),
  rw <- mul_assoc_int_rw aden bden (int_mul cden (int_mul bnum (int_mul cnum (int_mul cden aden)))), rw mul_comm_int_rw aden bden, rw mul_assoc_int_rw bden aden (int_mul cden (int_mul bnum (int_mul cnum (int_mul cden aden)))), rw <- mul_assoc_int_rw aden cden (int_mul bnum (int_mul cnum (int_mul cden aden))), rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden (int_mul bnum (int_mul cnum (int_mul cden aden))), rw <- mul_assoc_int_rw aden bnum (int_mul cnum (int_mul cden aden)), rw mul_comm_int_rw aden bnum, rw mul_assoc_int_rw bnum aden (int_mul cnum (int_mul cden aden)), rw <- mul_assoc_int_rw aden cnum (int_mul cden aden), rw mul_comm_int_rw aden cnum, rw mul_assoc_int_rw cnum aden (int_mul cden aden), rw <- mul_assoc_int_rw aden cden aden, rw mul_comm_int_rw aden cden, rw mul_assoc_int_rw cden aden aden, rw <- mul_assoc_int_rw bden cden (int_mul bnum (int_mul cnum (int_mul cden (int_mul aden aden)))), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul bnum (int_mul cnum (int_mul cden (int_mul aden aden)))), rw <- mul_assoc_int_rw bden bnum (int_mul cnum (int_mul cden (int_mul aden aden))), rw mul_comm_int_rw bden bnum, rw mul_assoc_int_rw bnum bden (int_mul cnum (int_mul cden (int_mul aden aden))), rw <- mul_assoc_int_rw bden cnum (int_mul cden (int_mul aden aden)), rw mul_comm_int_rw bden cnum, rw mul_assoc_int_rw cnum bden (int_mul cden (int_mul aden aden)), rw <- mul_assoc_int_rw bden cden (int_mul aden aden), rw mul_comm_int_rw bden cden, rw mul_assoc_int_rw cden bden (int_mul aden aden), rw <- mul_assoc_int_rw bnum cnum (int_mul cden (int_mul bden (int_mul aden aden))), rw mul_comm_int_rw bnum cnum, rw mul_assoc_int_rw cnum bnum (int_mul cden (int_mul bden (int_mul aden aden))), rw <- mul_assoc_int_rw bnum cden (int_mul bden (int_mul aden aden)), rw mul_comm_int_rw bnum cden, rw mul_assoc_int_rw cden bnum (int_mul bden (int_mul aden aden)), rw <- mul_assoc_int_rw cden cnum (int_mul cden (int_mul bnum (int_mul bden (int_mul aden aden)))), rw mul_comm_int_rw cden cnum, rw mul_assoc_int_rw cnum cden (int_mul cden (int_mul bnum (int_mul bden (int_mul aden aden)))),
  exact int_equal_refl (int_add (int_mul cnum (int_mul cden (int_mul cden (int_mul bden (int_mul bden (int_mul anum aden)))))) (int_mul cnum (int_mul cden (int_mul cden (int_mul bnum (int_mul bden (int_mul aden aden))))))),
end

lemma rat_mul_distrib_inv (a b c : myrat) : rat_eq (rat_add (rat_mul a c) (rat_mul b c)) (rat_mul (rat_add a b) c) :=
begin
  apply rat_eq_comm _ _, exact rat_mul_distrib a b c,
end

lemma rat_mul_distrib_alt (a b c : myrat) : rat_eq (rat_mul a (rat_add b c)) (rat_add (rat_mul a b) (rat_mul a c)) :=
begin
  rw rat_mul_comm, rw rat_mul_comm a b, rw rat_mul_comm a c, exact rat_mul_distrib b c a,
end

lemma rat_one_mul (a b : myrat) : rat_eq a rat_one -> rat_eq (rat_mul a b) b :=
begin
  intros h, exact rat_eq_comm b (rat_mul a b) (rat_mul_one a b h),
end

def rat_reciprocal : myrat -> myrat
| (rat num den) := (rat (int_mul den den) (int_mul num den))
/- We can't just do (rat den num) because then reciprocal (1/0) is 0/1, so we
   get a defined value from an undefined value.-/

lemma reciprocal_mul_inv (a : myrat) : rat_eq rat_one (rat_mul a (rat_reciprocal a)) :=
begin
  cases a with anum aden, unfold rat_reciprocal, unfold rat_mul, unfold rat_one, unfold rat_eq,
  by_cases (iszero aden),
    right, right, exact mul_zero_int aden (int_mul anum aden) h,

    left, rw mul_comm_int_rw int_one (int_mul aden (int_mul anum aden)),
    rw mul_comm_int_rw int_one (int_mul anum (int_mul aden aden)),
    apply (mul_eq_alt int_one (int_mul aden (int_mul anum aden)) (int_mul anum (int_mul aden aden))),
    rw <- mul_assoc_int_rw anum aden aden,
    rw mul_comm_int_rw aden (int_mul anum aden),
    exact int_equal_refl (int_mul (int_mul anum aden) aden),
end

lemma reciprocal_inv_mul (a : myrat) : rat_eq (rat_mul a (rat_reciprocal a)) rat_one :=
begin
  exact rat_eq_comm rat_one (rat_mul a (rat_reciprocal a)) (reciprocal_mul_inv a),
end

lemma reciprocal_mul_cancel (a b : myrat) : rat_eq a (rat_mul a (rat_mul b (rat_reciprocal b))) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_reciprocal, unfold rat_mul, unfold rat_eq,
  left, rw <- mul_assoc_int_rw bden bnum bden, rw mul_comm_int_rw bden bnum, rw mul_assoc_int_rw bnum bden bden,
  rw <- mul_assoc_int_rw anum aden (int_mul bnum (int_mul bden bden)), rw mul_comm_int_rw anum aden,
  repeat {rw mul_assoc_int_rw}, exact int_equal_refl _,
end

lemma reciprocal_def (a : myrat) : (defined a) -> ¬(iszero_rat a) -> (defined (rat_reciprocal a)) :=
begin
  cases a with anum aden, unfold rat_reciprocal, unfold defined, unfold iszero_rat, intros,
  by_cases h1 : iszero anum,
    have tmp : iszero anum \/ iszero aden, left, exact h1,
    cc,
  by_cases h2 : iszero aden,
    have tmp : iszero anum \/ iszero aden, right, exact h2,
    cc,
  exact mul_nonzero_int anum aden h1 h2,
end

lemma reciprocal_undef_undef (a : myrat) : ¬(defined a) -> ¬(defined (rat_reciprocal a)) :=
begin
  cases a with anum aden, unfold rat_reciprocal, unfold defined, intros,
  by_cases h1 : (iszero aden),
    by_cases h2 : ¬(iszero (int_mul anum aden)),
      have h3 : iszero (int_mul anum aden),
        exact mul_zero_int_alt aden anum h1,
      cc,
      exact h2,
    cc,
end

lemma reciprocal_zero_undef (a : myrat) : (iszero_rat a) -> ¬(defined (rat_reciprocal a)) :=
begin
  cases a with anum aden, unfold rat_reciprocal, unfold defined, unfold iszero_rat, intros h,
  cases h with h,
  by_cases h1 : ¬(iszero (int_mul anum aden)),
    have h2 : iszero (int_mul anum aden),
      exact mul_zero_int anum aden h,
    cc,
    cc,
  have h1 : iszero (int_mul anum aden), exact mul_zero_int_alt aden anum h,
  cc,
end

lemma reciprocal_mul_inv_alt (a b : myrat) : rat_eq a (rat_mul (rat_mul a b) (rat_reciprocal b)) :=
begin
  rw rat_mul_assoc, apply rat_eq_comm _ _, rw rat_mul_comm _ _, by_cases h1 : (defined b), by_cases h2 : (iszero_rat b),
    exact undef_eq (rat_mul (rat_mul b (rat_reciprocal b)) a) a (rat_mul_undef (rat_mul b (rat_reciprocal b)) a (rat_undef_mul b (rat_reciprocal b) (reciprocal_zero_undef b h2))),
    have tmp : defined (rat_mul b (rat_reciprocal b)),
       exact rat_mul_def b (rat_reciprocal b) h1 (reciprocal_def b h1 h2),
    have tmp2 : defined rat_one,
      unfold rat_one, unfold defined, unfold int_one, unfold iszero, unfold nat_one, cc,
    apply mul_sub_rat rat_one (rat_mul b (rat_reciprocal b)) a a tmp2 (reciprocal_mul_inv b),
    rw rat_mul_comm,  rw rat_mul_one_rw, exact rat_eq_refl a,

    exact undef_eq (rat_mul (rat_mul b (rat_reciprocal b)) a) a (rat_mul_undef (rat_mul b (rat_reciprocal b)) a (rat_mul_undef b (rat_reciprocal b) h1)),
end

lemma reciprocal_eq (a b : myrat) : (rat_eq a b) -> (rat_eq (rat_reciprocal a) (rat_reciprocal b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_reciprocal, unfold rat_eq, intros h, cases h,
    left, rw mul_comm_int_rw anum aden, repeat {rw mul_assoc_int_rw},
    apply mul_eq aden (int_mul aden (int_mul bnum bden)) (int_mul anum (int_mul bden bden)),
    repeat {rw <- mul_assoc_int_rw},
    apply mul_eq_alt bden (int_mul aden bnum) (int_mul anum bden),
    exact int_eq_comm _ _ h,

    cases h, right, left, exact mul_zero_int_alt aden anum h,
             right, right, exact mul_zero_int_alt bden bnum h,
end

/- We'll need this to cancel the /2a in the quadratic formula.-/
lemma half_reciprocal_mul (a : myrat) : rat_eq (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) :=
begin
  unfold rat_two, cases a with num den, unfold rat_add, unfold rat_reciprocal, unfold rat_mul, unfold rat_eq, left,
  unfold int_one, unfold int_mul, unfold mymul, unfold myadd, unfold nat_one, unfold mymul, unfold myadd,
  rw <- mul_two_int, rw mul_one_int_rw_alt,
  repeat {rw mul_assoc_int_rw},
  rw <- mul_assoc_int_rw den (int zero.mysucc.mysucc zero) (int_mul num (int_mul den (int_mul den den))),
  rw mul_comm_int_rw den (int zero.mysucc.mysucc zero),
  repeat {rw mul_assoc_int_rw},
  rw <- mul_assoc_int_rw den num (int_mul den (int_mul den den)),
  rw mul_comm_int_rw den num, repeat {rw mul_assoc_int_rw},
  exact int_equal_refl _,
end

def negate_rat : myrat -> myrat
| (rat num den) := (rat (negative num) den)

lemma negate_def (a : myrat) : (defined a) -> (defined (negate_rat a)) :=
begin
  cases a with anum aden, unfold negate_rat, unfold defined, cc,
end

lemma negate_undef (a : myrat) : ¬(defined a) -> ¬(defined (negate_rat a)) :=
begin
  cases a with anum aden, unfold negate_rat, unfold defined, cc,
end

lemma negate_eq_rat (a b : myrat) : (rat_eq a b) -> (rat_eq (negate_rat a) (negate_rat b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold negate_rat, unfold rat_eq, intros h, cases h, left,
    rw mul_comm_int_rw (negative anum) bden, repeat {rw mul_negative},
    rw mul_comm_int_rw bden anum, exact negative_eq (int_mul anum bden) (int_mul aden bnum) h,

    cc,
end

lemma double_negate (a : myrat) : (negate_rat (negate_rat a)) = a :=
begin
  cases a with anum aden, unfold negate_rat, cases anum with aplus aminus, unfold negative,
end

lemma mul_negate (a b : myrat) : rat_eq (rat_mul a (negate_rat b)) (negate_rat (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_mul, unfold negate_rat,
  rw <- mul_negative anum bnum,
  unfold rat_mul,
  exact rat_eq_refl (rat (int_mul anum (negative bnum)) (int_mul aden bden)),
end

lemma mul_negate_rw (a b : myrat) : (rat_mul a (negate_rat b)) = (negate_rat (rat_mul a b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_mul, unfold negate_rat,
  rw <- mul_negative anum bnum,
  unfold rat_mul,
end

lemma mul_negate_alt_rw (a b : myrat) : (rat_mul (negate_rat a) b) = (rat_mul a (negate_rat b)) :=
begin
  cases a with anum aden, cases b with bnum bden, unfold negate_rat, unfold rat_mul,
  rw mul_negative_alt anum bnum,
end

lemma add_negate_rat (a : myrat) : rat_eq (rat_add a (negate_rat a)) rat_zero :=
begin
  cases a with anum aden, unfold negate_rat, unfold rat_zero, unfold rat_add, unfold rat_eq,
  left, rw mul_one_int_rw, rw mul_comm_int_rw (negative anum) aden, rw mul_negative aden anum,
  have h1 : int_equal int_zero (int_add (int_mul anum aden) (negative (int_mul anum aden))),
    exact add_to_negative (int_mul anum aden),
  have h2 : int_equal (int_mul (int_mul aden aden) int_zero) int_zero,
    exact mul_zero_int_zero (int_mul aden aden),
  have h3 : int_equal (int_mul (int_mul aden aden) int_zero) (int_add (int_mul anum aden) (negative (int_mul anum aden))),
    exact int_eq_trans (int_mul (int_mul aden aden) int_zero) int_zero (int_add (int_mul anum aden) (negative (int_mul anum aden))) h2 h1,
  rw mul_comm_int_rw aden anum,
  exact int_eq_comm (int_mul (int_mul aden aden) int_zero) (int_add (int_mul anum aden) (negative (int_mul anum aden))) h3,
end

lemma add_negate_rat_alt (a : myrat) : iszero_rat (rat_add a (negate_rat a)) :=
begin
  cases a with anum aden, unfold negate_rat, unfold rat_add, unfold iszero_rat,
  rw mul_comm_int_rw (negative anum) aden, rw mul_negative aden anum, rw mul_comm_int_rw anum aden, left,
  exact add_to_negative_alt (int_mul aden anum),
end

lemma iszero_mul_rat (a b : myrat) : ¬(iszero_rat b) -> (defined b) -> (iszero_rat (rat_mul a b)) -> iszero_rat a :=
begin
  cases a with anum aden, cases b with bnum bden, unfold rat_mul, unfold iszero_rat, unfold defined, intros h1 h2 h3,
  by_cases h4 : iszero bnum,
    cc, cases h3,
      left, rw mul_comm_int_rw at h3, exact mul_result_zero_int bnum anum h4 h3,
      right, exact mul_result_zero_int_rev aden bden h2 h3,
end

/- I don't know if you'd really call it a "formula", but the solution to ax + b = 0 is
    x = -b/a.  We may as well prove that, right?-/
def linear_formula : myrat -> myrat -> myrat
| a b := negate_rat (rat_mul b (rat_reciprocal a))

lemma linear_formula_works (a b : myrat) : rat_eq (rat_add (rat_mul a (linear_formula a b)) b) rat_zero :=
begin
  unfold linear_formula, repeat {rw <- mul_negate_rw},
  rw <- rat_mul_assoc a b (negate_rat (rat_reciprocal a)),
  rw rat_mul_comm a b,
  rw rat_mul_assoc b a (negate_rat (rat_reciprocal a)),
  rw mul_negate_rw a (rat_reciprocal a),
  rw <- mul_negate_alt_rw b (rat_mul a (rat_reciprocal a)),
  have h1 : rat_eq (rat_mul a (rat_reciprocal a)) rat_one,
    exact rat_eq_comm rat_one (rat_mul a (rat_reciprocal a)) (reciprocal_mul_inv a),
  by_cases h2 : (defined a),
    by_cases h3 : (iszero_rat a),
      have h4 : ¬defined (rat_reciprocal a),
        exact reciprocal_zero_undef a h3,
      have h5 : ¬defined (rat_mul a (rat_reciprocal a)),
        exact rat_undef_mul a (rat_reciprocal a) h4,
      have h6 : ¬defined (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))),
        exact rat_undef_mul (negate_rat b) (rat_mul a (rat_reciprocal a)) h5,
      have h7 : ¬defined (rat_add (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) b),
        exact rat_add_undef (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) b h6,
      exact undef_eq (rat_add (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) b) rat_zero h7,

      have h4 : rat_eq (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) (negate_rat b),
        rw rat_mul_comm (negate_rat b) (rat_mul a (rat_reciprocal a)),
        exact rat_one_mul (rat_mul a (rat_reciprocal a)) (negate_rat b) h1,
      have h5 : defined (rat_mul a (rat_reciprocal a)),
        exact rat_mul_def a (rat_reciprocal a) h2 (reciprocal_def a h2 h3),
      have h6 : rat_eq (rat_add (negate_rat b) b) rat_zero,
        rw rat_add_comm, exact add_negate_rat b,
      have h7 : rat_eq (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) (negate_rat b),
         rw rat_mul_comm, exact rat_one_mul (rat_mul a (rat_reciprocal a)) (negate_rat b) (reciprocal_inv_mul a),
      by_cases h8 : (defined b),
        exact add_sub_rat (negate_rat b) (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) b rat_zero (negate_def b h8) (rat_eq_comm (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) (negate_rat b) h7) h6,

        rw rat_add_comm,
        exact undef_eq (rat_add b (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a)))) rat_zero (rat_add_undef b (rat_mul (negate_rat b) (rat_mul a (rat_reciprocal a))) h8),

    rw rat_mul_comm (negate_rat b) (rat_mul a (rat_reciprocal a)),
    exact undef_eq (rat_add (rat_mul (rat_mul a (rat_reciprocal a)) (negate_rat b)) b) rat_zero (rat_add_undef (rat_mul (rat_mul a (rat_reciprocal a)) (negate_rat b)) b (rat_mul_undef (rat_mul a (rat_reciprocal a)) (negate_rat b) (rat_mul_undef a (rat_reciprocal a) h2))),
end

/- OK.  a + (b * sqrt(c)) is not a field.
   However, a + (b * sqrt(c)) where c is constant IS a field.
   Ergo, we need to define a type constructor where c is part of the type.-/
inductive rat_plus_sqrt (a : myrat) : Type
| rps : myrat -> myrat -> rat_plus_sqrt
/- A value (a, b) of type (rat_plus_sqrt c) represents the number a + (b * sqrt(c))
   This means that operations are only defined when the values inside the square roots are the same.-/
open rat_plus_sqrt

def zero_rps (k : myrat) : rat_plus_sqrt k := (rps rat_zero rat_zero)

def defined_rps (k : myrat) : rat_plus_sqrt k -> Prop
| (rps a b) := (defined a) /\ (defined b) /\ (defined k)

def rps_equal (k : myrat) : rat_plus_sqrt k -> rat_plus_sqrt k -> Prop
| (rps a b) (rps c d) := (rat_eq a c) /\ (rat_eq b d)
/- There are some niche scenarios where this could be wrong.
  E.g. 3 + 0√4 compared to 1 + 1√4 - they are equal as real numbers but not by the above.
  However, as we are treating roots as black boxes, it simplifies things dramatically to not
  do those sorts of comparisons, and for the sake of provign the quadratic formula it doesn't matter.-/

def iszero_rps (k : myrat) : rat_plus_sqrt k -> Prop
| (rps a b) := (iszero_rat a) /\ (iszero_rat b)
/- Technically this is slightly too strict, as for example 6 + (-3)√4 = 0 but is not detected
    as zero by the above.  However this will do for the purposes of checking the quadratic formula.-/

/- The below definitions cannot be proven to be correct from within Lean, as we are simply defining
   √k to be the number that gives k when it is multiplied by itself, so Lean knows of no other properties of it.
   View the comments for an explanation of how each one follows from the field axioms.
   Therefore the only real assumptions that we are making here is that the square root of a given
   number exists (which it does if we allow complex numbers) and that the complex numbers are a field.-/
def add_rps (k : myrat) : rat_plus_sqrt k -> rat_plus_sqrt k -> rat_plus_sqrt k
| (rps a b) (rps c d) := (rps (rat_add a c) (rat_add b d))
/- This is straightforwardly true because addition is associative and commutative.
    (a + bq) + (c + dq) = (a + c) + bq + dq no matter what properties q might have.
    And then because multiplication distributes over addition we can write that as (a + c) + (b + d)q-/

def negate_rps (k : myrat) : rat_plus_sqrt k -> rat_plus_sqrt k
| (rps a b) := (rps (negate_rat a) (negate_rat b))
/- Simple.  Multiplication distributes over addition, so multiplying both pats of a sum by -1
   is equivalent to multiplying the whole thing by -1.-/

def mul_rps (k : myrat) : rat_plus_sqrt k -> rat_plus_sqrt k -> rat_plus_sqrt k
| (rps a b) (rps c d) := (rps (rat_add (rat_mul a c) (rat_mul b (rat_mul d k)))
                              (rat_add (rat_mul a d) (rat_mul b c)))
/- Multiplication distributes over addition.  Ergo
      (a + b√k)(c + d√k) = a(c + d√k) + b√k(c + d√k) = ac + ad√k + bc√k + bd√k√k
   Addition is commutative and associative, so we can rearrange terms...
      = ac + bd√k√k + ad√k + bc√k
   And then √k√k = k by definition.
      = ac + bdk + (ad + bd)√k
   Ergo the above equation makes no assumptions apart from the field axioms and the definition of a square root.-/

def add_rps_to_rat (k : myrat) : rat_plus_sqrt k -> myrat -> rat_plus_sqrt k
| (rps a b) c := (rps (rat_add a c) b)
/- Trivial by commutativity and associativity of addition.-/

def mul_rps_by_rat (k : myrat) : rat_plus_sqrt k -> myrat -> rat_plus_sqrt k
| (rps a b) c := (rps (rat_mul a c) (rat_mul b c))
/- Again, distribution and commutativity of multiplication.  (a + b√k)c = ac + b(√k)c = ac + bc√k-/

def sqrt (k : myrat) : rat_plus_sqrt k := (rps rat_zero rat_one)
/- Follows easily from how we defined the rat_plus_sqrt type.-/

lemma add_zero_rps_alt (k : myrat) (a : rat_plus_sqrt k) : (add_rps k a (zero_rps k)) = a :=
begin
  unfold zero_rps, cases a with rata roota, unfold add_rps, repeat {rw rat_add_zero_alt},
end

lemma add_comm_rps (k : myrat) (a b : rat_plus_sqrt k) : (add_rps k a b) = (add_rps k b a) :=
begin
  cases a with rata roota, cases b with ratb rootb, unfold add_rps,
  rw rat_add_comm rata ratb, rw rat_add_comm roota rootb,
end

lemma add_assoc_rps (k : myrat) (a b c : rat_plus_sqrt k) :
        (add_rps k (add_rps k a b) c) = (add_rps k a (add_rps k b c)) :=
begin
  cases a with rata roota, cases b with ratb rootb, cases c with ratc rootc,
  unfold add_rps, rw rat_add_assoc rata ratb ratc, rw rat_add_assoc roota rootb rootc,
end

lemma add_zero_rps (k : myrat) (a b : rat_plus_sqrt k) :
    (iszero_rps k a) -> (rps_equal k (add_rps k a b) b) :=
begin
  cases a with rata roota, cases b with ratb rootb,
  unfold add_rps, unfold iszero_rps, unfold rps_equal, intros h, cases h with h1 h2, split,
    exact rat_add_zero rata ratb h1,
    exact rat_add_zero roota rootb h2,
end

lemma add_def_rps (k : myrat) (a b : rat_plus_sqrt k) :
  (defined_rps k a) -> (defined_rps k b) -> (defined_rps k (add_rps k a b)) :=
begin
  cases a with rata roota, cases b with ratb rootb, unfold add_rps, unfold defined_rps, intros h1 h2,
  cases h1 with h11 h12, cases h12 with h12 h13, cases h2 with h21 h22, cases h22 with h22 h23, split,
  exact rat_add_def rata ratb h11 h21, split,
  exact rat_add_def roota rootb h12 h22, exact h13,
end

/- Woo classical logic! -/
lemma negate_and (a b c : Prop) : ¬(a /\ b /\ c) -> (¬a \/ ¬b \/ ¬c) :=
begin
  intros h, by_cases ha : a, by_cases hb : b, by_cases hc : c,
    have h1 : (a /\ b /\ c), split, exact ha, split, exact hb, exact hc, cc,
    right, right, cc,
    right, left, cc,
    left, cc,
end

lemma add_undef_rps (k : myrat) (a b : rat_plus_sqrt k) :
  ¬(defined_rps k a) -> ¬(defined_rps k (add_rps k a b)) :=
begin
  cases a with rata roota, cases b with ratb rootb, unfold add_rps, unfold defined_rps, intros h,
  have h1 : (¬(defined rata) \/ ¬(defined roota) \/ ¬(defined k)),
    exact negate_and (defined rata) (defined roota) (defined k) h,
  cases h1,
    intro h2, cases h2 with h2 _, exact rat_add_undef rata ratb h1 h2,
    cases h1,
      intro h2, cases h2 with _ h2, cases h2 with h2 _, exact rat_add_undef roota rootb h1 h2,
      intro h2, cases h2 with _ h2, cases h2 with _ h2, exact h1 h2,
end

lemma negate_add_inv_rps (k : myrat) (a : rat_plus_sqrt k) :
  iszero_rps k (add_rps k a (negate_rps k a)) :=
begin
  cases a with rata roota, unfold negate_rps, unfold add_rps, unfold iszero_rps, split,
    exact add_negate_rat_alt rata,
    exact add_negate_rat_alt roota,
end

lemma mul_comm_rps (k : myrat) (a b : rat_plus_sqrt k) : (mul_rps k a b) = (mul_rps k b a) :=
begin
  cases a with rata roota, cases b with ratb rootb, unfold mul_rps,
  rw <- rat_mul_assoc roota rootb k, rw rat_mul_comm roota rootb, rw rat_mul_assoc rootb roota k,
  rw rat_add_comm (rat_mul ratb roota) (rat_mul rootb rata),
  rw rat_mul_comm ratb roota, rw rat_mul_comm rata rootb,
  rw rat_mul_comm rata ratb,
end

lemma mul_assoc_rps (k : myrat) (a b c : rat_plus_sqrt k) :
  rps_equal k (mul_rps k (mul_rps k a b) c) (mul_rps k a (mul_rps k b c)) :=
begin
  cases a with rata roota, cases b with ratb rootb, cases c with ratc rootc,
  unfold mul_rps, unfold rps_equal, split,
  repeat {rw rat_add_assoc},
  /- Using python for something a bit different this time.
     The proof is trivial for all the cases where one of the numbers isn't defined, but we don't
     want to have to through them all manually.  Much better to leave that bit to the machine.-/
  by_cases ratc_def_tmp : (¬defined ratc), rw rat_mul_comm (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc, exact undef_eq (rat_add (rat_mul ratc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)))) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul ratc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)))) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef ratc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc_def_tmp)), have ratc_defined : (defined ratc), cc, clear ratc_def_tmp, by_cases ratb_def_tmp : (¬defined ratb), rw rat_mul_comm rata ratb, exact undef_eq (rat_add (rat_mul (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) ratc (rat_add_undef (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k)) (rat_mul_undef ratb rata ratb_def_tmp)))), have ratb_defined : (defined ratb), cc, clear ratb_def_tmp, by_cases rootb_def_tmp : (¬defined rootb), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), rw rat_mul_comm roota (rat_mul rootb k), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) ratc (rat_add_undef (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb) (rat_mul_undef (rat_mul rootb k) roota (rat_mul_undef rootb k rootb_def_tmp))))), have rootb_defined : (defined rootb), cc, clear rootb_def_tmp, by_cases roota_def_tmp : (¬defined roota), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) ratc (rat_add_undef (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb) (rat_mul_undef roota (rat_mul rootb k) roota_def_tmp)))), have roota_defined : (defined roota), cc, clear roota_def_tmp, by_cases rata_def_tmp : (¬defined rata), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc (rat_add_undef (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)) (rat_mul_undef rata ratb rata_def_tmp)))), have rata_defined : (defined rata), cc, clear rata_def_tmp, by_cases rootc_def_tmp : (¬defined rootc), rw rat_add_comm (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)), rw rat_mul_comm (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k), exact undef_eq (rat_add (rat_mul (rat_mul rootc k) (rat_add (rat_mul rata rootb) (rat_mul roota ratb))) (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_mul rootc k) (rat_add (rat_mul rata rootb) (rat_mul roota ratb))) (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul_undef (rat_mul rootc k) (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul_undef rootc k rootc_def_tmp))), have rootc_defined : (defined rootc), cc, clear rootc_def_tmp, by_cases k_def_tmp : (¬defined k), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), rw rat_mul_comm roota (rat_mul rootb k), rw rat_mul_comm rootb k, exact undef_eq (rat_add (rat_mul (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_undef (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) ratc (rat_add_undef (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb) (rat_mul_undef (rat_mul k rootb) roota (rat_mul_undef k rootb k_def_tmp))))), have k_defined : (defined k), cc, clear k_def_tmp,
  /- Basically, we now have hypotheses "x_defined : defined X" for every rational number in the proof.-/
  apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_def (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) ((rat_add_def (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc) ((rat_mul_def (rat_mul rata ratb) ratc ((rat_mul_def rata ratb (rata_defined) (ratb_defined))) (ratc_defined))) ((rat_mul_def (rat_mul roota (rat_mul rootb k)) ratc ((rat_mul_def roota (rat_mul rootb k) (roota_defined) ((rat_mul_def rootb k (rootb_defined) (k_defined))))) (ratc_defined))))) ((rat_mul_def (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k) ((rat_add_def (rat_mul rata rootb) (rat_mul roota ratb) ((rat_mul_def rata rootb (rata_defined) (rootb_defined))) ((rat_mul_def roota ratb (roota_defined) (ratb_defined))))) ((rat_mul_def rootc k (rootc_defined) (k_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) ratc) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_mul_distrib (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)) ratc)), rw rat_add_comm (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc))) (rat_add (rat_mul rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add_def (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) ((rat_add_def (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k)) ((rat_mul_def (rat_mul rata rootb) (rat_mul rootc k) ((rat_mul_def rata rootb (rata_defined) (rootb_defined))) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) ((rat_mul_def (rat_mul roota ratb) (rat_mul rootc k) ((rat_mul_def roota ratb (roota_defined) (ratb_defined))) ((rat_mul_def rootc k (rootc_defined) (k_defined))))))) ((rat_add_def (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc) ((rat_mul_def (rat_mul rata ratb) ratc ((rat_mul_def rata ratb (rata_defined) (ratb_defined))) (ratc_defined))) ((rat_mul_def (rat_mul roota (rat_mul rootb k)) ratc ((rat_mul_def roota (rat_mul rootb k) (roota_defined) ((rat_mul_def rootb k (rootb_defined) (k_defined))))) (ratc_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) (rat_mul rootc k)) (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc)) (rat_mul_distrib (rat_mul rata rootb) (rat_mul roota ratb) (rat_mul rootc k))),
  apply rat_eq_comm _ _, rw rat_mul_comm rata (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) rata) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc))) (rat_add_def (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k)) ((rat_add_def (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata) ((rat_mul_def (rat_mul ratb ratc) rata ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))) (rata_defined))) ((rat_mul_def (rat_mul rootb (rat_mul rootc k)) rata ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) (rata_defined))))) ((rat_mul_def roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k) (roota_defined) ((rat_mul_def (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k ((rat_add_def (rat_mul ratb rootc) (rat_mul rootb ratc) ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))) ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))))) (k_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) rata) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (rat_mul roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k)) (rat_mul_distrib (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)) rata)), rw rat_mul_comm roota (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k), rw rat_add_comm (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (rat_mul (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k) roota), apply rat_eq_trans (rat_add (rat_mul (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k) roota) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata))) (rat_add (rat_mul (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc))) (rat_add_def (rat_mul (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) ((rat_mul_def (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota ((rat_add_def (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k) ((rat_mul_def (rat_mul ratb rootc) k ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))) (k_defined))) ((rat_mul_def (rat_mul rootb ratc) k ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))) (k_defined))))) (roota_defined))) ((rat_add_def (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata) ((rat_mul_def (rat_mul ratb ratc) rata ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))) (rata_defined))) ((rat_mul_def (rat_mul rootb (rat_mul rootc k)) rata ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) (rata_defined))))))(add_eq_rat (rat_mul (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k) roota) (rat_mul (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (mul_eq_rat (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) k) (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota (rat_mul_distrib (rat_mul ratb rootc) (rat_mul rootb ratc) k))), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata))) (rat_add (rat_add (rat_mul (rat_mul (rat_mul ratb rootc) k) roota) (rat_mul (rat_mul (rat_mul rootb ratc) k) roota)) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) (rat_mul rootc k)) (rat_mul (rat_mul roota ratb) (rat_mul rootc k))) (rat_add (rat_mul (rat_mul rata ratb) ratc) (rat_mul (rat_mul roota (rat_mul rootb k)) ratc))) (rat_add_def (rat_add (rat_mul (rat_mul (rat_mul ratb rootc) k) roota) (rat_mul (rat_mul (rat_mul rootb ratc) k) roota)) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) ((rat_add_def (rat_mul (rat_mul (rat_mul ratb rootc) k) roota) (rat_mul (rat_mul (rat_mul rootb ratc) k) roota) ((rat_mul_def (rat_mul (rat_mul ratb rootc) k) roota ((rat_mul_def (rat_mul ratb rootc) k ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))) (k_defined))) (roota_defined))) ((rat_mul_def (rat_mul (rat_mul rootb ratc) k) roota ((rat_mul_def (rat_mul rootb ratc) k ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))) (k_defined))) (roota_defined))))) ((rat_add_def (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata) ((rat_mul_def (rat_mul ratb ratc) rata ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))) (rata_defined))) ((rat_mul_def (rat_mul rootb (rat_mul rootc k)) rata ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) (rata_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k)) roota) (rat_add (rat_mul (rat_mul (rat_mul ratb rootc) k) roota) (rat_mul (rat_mul (rat_mul rootb ratc) k) roota)) (rat_add (rat_mul (rat_mul ratb ratc) rata) (rat_mul (rat_mul rootb (rat_mul rootc k)) rata)) (rat_mul_distrib (rat_mul (rat_mul ratb rootc) k) (rat_mul (rat_mul rootb ratc) k) roota)),
  /- The above lines do all the distributive rewrites.  This was trivial for ints, but is less trivial for rats.-/

  repeat {rw rat_mul_assoc}, repeat {rw rat_add_assoc},
  rw <- rat_mul_assoc rootc k roota, rw rat_mul_comm rootc k, rw rat_mul_assoc k rootc roota, rw rat_mul_comm rootc roota, rw <- rat_mul_assoc ratb k (rat_mul roota rootc), rw rat_mul_comm ratb k, rw rat_mul_assoc k ratb (rat_mul roota rootc), rw <- rat_mul_assoc rootb ratc (rat_mul k roota), rw rat_mul_comm rootb ratc, rw rat_mul_assoc ratc rootb (rat_mul k roota), rw <- rat_mul_assoc rootb k roota, rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb roota, rw rat_mul_comm rootb roota, rw <- rat_mul_assoc ratc k (rat_mul roota rootb), rw rat_mul_comm ratc k, rw rat_mul_assoc k ratc (rat_mul roota rootb), rw rat_mul_comm ratc rata, rw <- rat_mul_assoc ratb rata ratc, rw rat_mul_comm ratb rata, rw rat_mul_assoc rata ratb ratc, rw <- rat_mul_assoc rootc k rata, rw rat_mul_comm rootc k, rw rat_mul_assoc k rootc rata, rw rat_mul_comm rootc rata, rw <- rat_mul_assoc rootb k (rat_mul rata rootc), rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb (rat_mul rata rootc), rw <- rat_mul_assoc rootb rata rootc, rw rat_mul_comm rootb rata, rw rat_mul_assoc rata rootb rootc, rw rat_add_comm (rat_add (rat_add (rat_mul k (rat_mul ratb (rat_mul roota rootc))) (rat_mul k (rat_mul ratc (rat_mul roota rootb)))) (rat_mul rata (rat_mul ratb ratc))) (rat_mul k (rat_mul rata (rat_mul rootb rootc))),
  rw <- rat_mul_assoc rootb k rootc, rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb rootc, rw <- rat_mul_assoc rata k (rat_mul rootb rootc), rw rat_mul_comm rata k, rw rat_mul_assoc k rata (rat_mul rootb rootc), rw <- rat_mul_assoc roota ratb (rat_mul k rootc), rw rat_mul_comm roota ratb, rw rat_mul_assoc ratb roota (rat_mul k rootc), rw <- rat_mul_assoc roota k rootc, rw rat_mul_comm roota k, rw rat_mul_assoc k roota rootc, rw <- rat_mul_assoc ratb k (rat_mul roota rootc), rw rat_mul_comm ratb k, rw rat_mul_assoc k ratb (rat_mul roota rootc), rw <- rat_mul_assoc rootb k ratc, rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb ratc, rw rat_mul_comm rootb ratc, rw <- rat_mul_assoc roota k (rat_mul ratc rootb), rw rat_mul_comm roota k, rw rat_mul_assoc k roota (rat_mul ratc rootb), rw <- rat_mul_assoc roota ratc rootb, rw rat_mul_comm roota ratc, rw rat_mul_assoc ratc roota rootb,
  repeat {rw <- rat_add_assoc}, rw rat_add_comm (rat_mul rata (rat_mul ratb ratc)) (rat_mul k (rat_mul ratc (rat_mul roota rootb))),
  exact rat_eq_refl _,


  by_cases k_def_tmp : (¬defined k), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), rw rat_mul_comm roota (rat_mul rootb k), rw rat_mul_comm rootb k, exact undef_eq (rat_add (rat_mul (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef (rat_add (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb)) rootc (rat_add_undef (rat_mul (rat_mul k rootb) roota) (rat_mul rata ratb) (rat_mul_undef (rat_mul k rootb) roota (rat_mul_undef k rootb k_def_tmp))))), have k_defined : (defined k), cc, clear k_def_tmp, by_cases rootb_def_tmp : (¬defined rootb), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), rw rat_mul_comm roota (rat_mul rootb k), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef (rat_add (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb)) rootc (rat_add_undef (rat_mul (rat_mul rootb k) roota) (rat_mul rata ratb) (rat_mul_undef (rat_mul rootb k) roota (rat_mul_undef rootb k rootb_def_tmp))))), have rootb_defined : (defined rootb), cc, clear rootb_def_tmp, by_cases rootc_def_tmp : (¬defined rootc), rw rat_mul_comm (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc, exact undef_eq (rat_add (rat_mul rootc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)))) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul rootc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)))) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef rootc (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc_def_tmp)), have rootc_defined : (defined rootc), cc, clear rootc_def_tmp, by_cases roota_def_tmp : (¬defined roota), rw rat_add_comm (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef (rat_add (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb)) rootc (rat_add_undef (rat_mul roota (rat_mul rootb k)) (rat_mul rata ratb) (rat_mul_undef roota (rat_mul rootb k) roota_def_tmp)))), have roota_defined : (defined roota), cc, clear roota_def_tmp, by_cases ratc_def_tmp : (¬defined ratc), rw rat_add_comm (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc), rw rat_mul_comm (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc, exact undef_eq (rat_add (rat_mul ratc (rat_add (rat_mul rata rootb) (rat_mul roota ratb))) (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul ratc (rat_add (rat_mul rata rootb) (rat_mul roota ratb))) (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul_undef ratc (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc_def_tmp)), have ratc_defined : (defined ratc), cc, clear ratc_def_tmp, by_cases rata_def_tmp : (¬defined rata), exact undef_eq (rat_add (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc (rat_add_undef (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)) (rat_mul_undef rata ratb rata_def_tmp)))), have rata_defined : (defined rata), cc, clear rata_def_tmp, by_cases ratb_def_tmp : (¬defined ratb), rw rat_mul_comm rata ratb, exact undef_eq (rat_add (rat_mul (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_undef (rat_mul (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_undef (rat_add (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k))) rootc (rat_add_undef (rat_mul ratb rata) (rat_mul roota (rat_mul rootb k)) (rat_mul_undef ratb rata ratb_def_tmp)))), have ratb_defined : (defined ratb), cc, clear ratb_def_tmp,
  apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc)) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_def (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) ((rat_add_def (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc) ((rat_mul_def (rat_mul rata ratb) rootc ((rat_mul_def rata ratb (rata_defined) (ratb_defined))) (rootc_defined))) ((rat_mul_def (rat_mul roota (rat_mul rootb k)) rootc ((rat_mul_def roota (rat_mul rootb k) (roota_defined) ((rat_mul_def rootb k (rootb_defined) (k_defined))))) (rootc_defined))))) ((rat_mul_def (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc ((rat_add_def (rat_mul rata rootb) (rat_mul roota ratb) ((rat_mul_def rata rootb (rata_defined) (rootb_defined))) ((rat_mul_def roota ratb (roota_defined) (ratb_defined))))) (ratc_defined))))(add_eq_rat (rat_mul (rat_add (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k))) rootc) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_mul_distrib (rat_mul rata ratb) (rat_mul roota (rat_mul rootb k)) rootc)), rw rat_add_comm (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc)) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc))) (rat_add (rat_mul rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc))) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add_def (rat_add (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc)) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) ((rat_add_def (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc) ((rat_mul_def (rat_mul rata rootb) ratc ((rat_mul_def rata rootb (rata_defined) (rootb_defined))) (ratc_defined))) ((rat_mul_def (rat_mul roota ratb) ratc ((rat_mul_def roota ratb (roota_defined) (ratb_defined))) (ratc_defined))))) ((rat_add_def (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc) ((rat_mul_def (rat_mul rata ratb) rootc ((rat_mul_def rata ratb (rata_defined) (ratb_defined))) (rootc_defined))) ((rat_mul_def (rat_mul roota (rat_mul rootb k)) rootc ((rat_mul_def roota (rat_mul rootb k) (roota_defined) ((rat_mul_def rootb k (rootb_defined) (k_defined))))) (rootc_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul rata rootb) (rat_mul roota ratb)) ratc) (rat_add (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc)) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc)) (rat_mul_distrib (rat_mul rata rootb) (rat_mul roota ratb) ratc)),
  apply rat_eq_comm _ _, rw rat_mul_comm rata (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) rata) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc)) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc))) (rat_add_def (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) ((rat_add_def (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata) ((rat_mul_def (rat_mul ratb rootc) rata ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))) (rata_defined))) ((rat_mul_def (rat_mul rootb ratc) rata ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))) (rata_defined))))) ((rat_mul_def roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) (roota_defined) ((rat_add_def (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)) ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))) ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))))))))(add_eq_rat (rat_mul (rat_add (rat_mul ratb rootc) (rat_mul rootb ratc)) rata) (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) (rat_mul roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_mul_distrib (rat_mul ratb rootc) (rat_mul rootb ratc) rata)), rw rat_mul_comm roota (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))), rw rat_add_comm (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) (rat_mul (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) roota), apply rat_eq_trans (rat_add (rat_mul (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) roota) (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata))) (rat_add (rat_add (rat_mul (rat_mul ratb ratc) roota) (rat_mul (rat_mul rootb (rat_mul rootc k)) roota)) (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata))) (rat_add (rat_add (rat_mul (rat_mul rata rootb) ratc) (rat_mul (rat_mul roota ratb) ratc)) (rat_add (rat_mul (rat_mul rata ratb) rootc) (rat_mul (rat_mul roota (rat_mul rootb k)) rootc))) (rat_add_def (rat_add (rat_mul (rat_mul ratb ratc) roota) (rat_mul (rat_mul rootb (rat_mul rootc k)) roota)) (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) ((rat_add_def (rat_mul (rat_mul ratb ratc) roota) (rat_mul (rat_mul rootb (rat_mul rootc k)) roota) ((rat_mul_def (rat_mul ratb ratc) roota ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))) (roota_defined))) ((rat_mul_def (rat_mul rootb (rat_mul rootc k)) roota ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) (roota_defined))))) ((rat_add_def (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata) ((rat_mul_def (rat_mul ratb rootc) rata ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))) (rata_defined))) ((rat_mul_def (rat_mul rootb ratc) rata ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))) (rata_defined))))))(add_eq_rat (rat_mul (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k))) roota) (rat_add (rat_mul (rat_mul ratb ratc) roota) (rat_mul (rat_mul rootb (rat_mul rootc k)) roota)) (rat_add (rat_mul (rat_mul ratb rootc) rata) (rat_mul (rat_mul rootb ratc) rata)) (rat_mul_distrib (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)) roota)),

  repeat {rw rat_mul_assoc}, repeat {rw rat_add_assoc},
  rw <- rat_mul_assoc rootc k roota, rw rat_mul_comm rootc k, rw rat_mul_assoc k rootc roota, rw rat_mul_comm rootc roota, rw <- rat_mul_assoc rootb k (rat_mul roota rootc), rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb (rat_mul roota rootc), rw <- rat_mul_assoc rootb roota rootc, rw rat_mul_comm rootb roota, rw rat_mul_assoc roota rootb rootc, rw rat_add_comm (rat_mul ratb (rat_mul ratc roota)) (rat_mul k (rat_mul roota (rat_mul rootb rootc))), rw rat_mul_comm rootc rata, rw <- rat_mul_assoc ratb rata rootc, rw rat_mul_comm ratb rata, rw rat_mul_assoc rata ratb rootc, rw <- rat_mul_assoc rootb ratc rata, rw rat_mul_comm rootb ratc, rw rat_mul_assoc ratc rootb rata, rw rat_mul_comm rootb rata, rw <- rat_mul_assoc ratc rata rootb, rw rat_mul_comm ratc rata, rw rat_mul_assoc rata ratc rootb,
  apply rat_eq_comm _ _, rw <- rat_mul_assoc roota ratb ratc, rw rat_mul_comm roota ratb, rw rat_mul_assoc ratb roota ratc, rw rat_mul_comm roota ratc, rw rat_add_comm (rat_add (rat_mul rata (rat_mul ratc rootb)) (rat_mul ratb (rat_mul ratc roota))) (rat_mul rata (rat_mul ratb rootc)), rw <- rat_mul_assoc rootb k rootc, rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb rootc, rw <- rat_mul_assoc roota k (rat_mul rootb rootc), rw rat_mul_comm roota k, rw rat_mul_assoc k roota (rat_mul rootb rootc), rw rat_add_comm (rat_add (rat_mul rata (rat_mul ratb rootc)) (rat_add (rat_mul rata (rat_mul ratc rootb)) (rat_mul ratb (rat_mul ratc roota)))) (rat_mul k (rat_mul roota (rat_mul rootb rootc))),
  rw rat_add_comm (rat_mul rata (rat_mul ratc rootb)) (rat_mul ratb (rat_mul ratc roota)),
  repeat {rw <- rat_add_assoc}, rw rat_add_assoc (rat_mul ratb (rat_mul ratc roota)) (rat_mul rata (rat_mul ratb rootc)) (rat_mul rata (rat_mul ratc rootb)),
  rw rat_add_comm (rat_mul ratb (rat_mul ratc roota)) (rat_mul rata (rat_mul ratb rootc)),
  repeat {rw rat_add_assoc}, exact rat_eq_refl _,
end

lemma mul_distrib_rps (k : myrat) (a b c : rat_plus_sqrt k) :
            rps_equal k (mul_rps k (add_rps k a b) c) (add_rps k (mul_rps k a c) (mul_rps k b c)) :=
begin
  cases a with rata roota, cases b with ratb rootb, cases c with ratc rootc,
  unfold add_rps, unfold mul_rps, unfold add_rps, unfold rps_equal, split,
    by_cases roota_def_tmp : (¬defined roota), rw rat_add_comm (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)), exact undef_eq (rat_add (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul (rat_add rata ratb) ratc)) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul (rat_add rata ratb) ratc) (rat_mul_undef (rat_add roota rootb) (rat_mul rootc k) (rat_add_undef roota rootb roota_def_tmp))), have roota_defined : (defined roota), cc, clear roota_def_tmp, by_cases ratb_def_tmp : (¬defined ratb), rw rat_add_comm rata ratb, exact undef_eq (rat_add (rat_mul (rat_add ratb rata) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul (rat_add ratb rata) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul_undef (rat_add ratb rata) ratc (rat_add_undef ratb rata ratb_def_tmp))), have ratb_defined : (defined ratb), cc, clear ratb_def_tmp, by_cases rata_def_tmp : (¬defined rata), exact undef_eq (rat_add (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul_undef (rat_add rata ratb) ratc (rat_add_undef rata ratb rata_def_tmp))), have rata_defined : (defined rata), cc, clear rata_def_tmp, by_cases ratc_def_tmp : (¬defined ratc), rw rat_mul_comm (rat_add rata ratb) ratc, exact undef_eq (rat_add (rat_mul ratc (rat_add rata ratb)) (rat_mul (rat_add roota rootb) (rat_mul rootc k))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul ratc (rat_add rata ratb)) (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul_undef ratc (rat_add rata ratb) ratc_def_tmp)), have ratc_defined : (defined ratc), cc, clear ratc_def_tmp, by_cases rootc_def_tmp : (¬defined rootc), rw rat_add_comm (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)), rw rat_mul_comm (rat_add roota rootb) (rat_mul rootc k), exact undef_eq (rat_add (rat_mul (rat_mul rootc k) (rat_add roota rootb)) (rat_mul (rat_add rata ratb) ratc)) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul (rat_mul rootc k) (rat_add roota rootb)) (rat_mul (rat_add rata ratb) ratc) (rat_mul_undef (rat_mul rootc k) (rat_add roota rootb) (rat_mul_undef rootc k rootc_def_tmp))), have rootc_defined : (defined rootc), cc, clear rootc_def_tmp, by_cases rootb_def_tmp : (¬defined rootb), rw rat_add_comm (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)), rw rat_add_comm roota rootb, exact undef_eq (rat_add (rat_mul (rat_add rootb roota) (rat_mul rootc k)) (rat_mul (rat_add rata ratb) ratc)) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_undef (rat_mul (rat_add rootb roota) (rat_mul rootc k)) (rat_mul (rat_add rata ratb) ratc) (rat_mul_undef (rat_add rootb roota) (rat_mul rootc k) (rat_add_undef rootb roota rootb_def_tmp))), have rootb_defined : (defined rootb), cc, clear rootb_def_tmp, by_cases k_def_tmp : (¬defined k), rw rat_add_comm (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k)), rw rat_mul_comm (rat_add roota rootb) (rat_mul rootc k), rw rat_mul_comm rootc k, exact undef_eq (rat_add (rat_mul (rat_mul k rootc) (rat_add roota rootb)) (rat_mul (rat_add rata ratb) ratc)) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul k rootc))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul k rootc)))) (rat_add_undef (rat_mul (rat_mul k rootc) (rat_add roota rootb)) (rat_mul (rat_add rata ratb) ratc) (rat_mul_undef (rat_mul k rootc) (rat_add roota rootb) (rat_mul_undef k rootc k_def_tmp))), have k_defined : (defined k), cc, clear k_def_tmp,
    apply rat_eq_trans (rat_add (rat_mul (rat_add rata ratb) ratc) (rat_mul (rat_add roota rootb) (rat_mul rootc k))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) (rat_mul (rat_add roota rootb) (rat_mul rootc k))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_def (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) (rat_mul (rat_add roota rootb) (rat_mul rootc k)) ((rat_add_def (rat_mul rata ratc) (rat_mul ratb ratc) ((rat_mul_def rata ratc (rata_defined) (ratc_defined))) ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))))) ((rat_mul_def (rat_add roota rootb) (rat_mul rootc k) ((rat_add_def roota rootb (roota_defined) (rootb_defined))) ((rat_mul_def rootc k (rootc_defined) (k_defined))))))(add_eq_rat (rat_mul (rat_add rata ratb) ratc) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_mul_distrib rata ratb ratc)), rw rat_add_comm (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) (rat_mul (rat_add roota rootb) (rat_mul rootc k)), apply rat_eq_trans (rat_add (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc))) (rat_add (rat_add (rat_mul roota (rat_mul rootc k)) (rat_mul rootb (rat_mul rootc k))) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc))) (rat_add (rat_add (rat_mul rata ratc) (rat_mul roota (rat_mul rootc k))) (rat_add (rat_mul ratb ratc) (rat_mul rootb (rat_mul rootc k)))) (rat_add_def (rat_add (rat_mul roota (rat_mul rootc k)) (rat_mul rootb (rat_mul rootc k))) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) ((rat_add_def (rat_mul roota (rat_mul rootc k)) (rat_mul rootb (rat_mul rootc k)) ((rat_mul_def roota (rat_mul rootc k) (roota_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))) ((rat_mul_def rootb (rat_mul rootc k) (rootb_defined) ((rat_mul_def rootc k (rootc_defined) (k_defined))))))) ((rat_add_def (rat_mul rata ratc) (rat_mul ratb ratc) ((rat_mul_def rata ratc (rata_defined) (ratc_defined))) ((rat_mul_def ratb ratc (ratb_defined) (ratc_defined))))))(add_eq_rat (rat_mul (rat_add roota rootb) (rat_mul rootc k)) (rat_add (rat_mul roota (rat_mul rootc k)) (rat_mul rootb (rat_mul rootc k))) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)) (rat_mul_distrib roota rootb (rat_mul rootc k))),
    repeat {rw rat_mul_assoc}, repeat {rw rat_add_assoc},
    rw rat_mul_comm rootc k, rw <- rat_mul_assoc roota k rootc, rw rat_mul_comm roota k, rw rat_mul_assoc k roota rootc,  rw <- rat_mul_assoc rootb k rootc, rw rat_mul_comm rootb k, rw rat_mul_assoc k rootb rootc,
    repeat {rw rat_mul_assoc}, repeat {rw <- rat_add_assoc},
    rw rat_add_comm (rat_mul k (rat_mul rootb rootc)) (rat_add (rat_mul rata ratc) (rat_mul ratb ratc)),
    repeat {rw rat_add_assoc}, rw rat_add_comm (rat_mul k (rat_mul roota rootc)) (rat_mul rata ratc),
    exact rat_eq_refl _,

    by_cases rootb_def_tmp : (¬defined rootb), rw rat_add_comm (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc), rw rat_add_comm roota rootb, exact undef_eq (rat_add (rat_mul (rat_add rootb roota) ratc) (rat_mul (rat_add rata ratb) rootc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul (rat_add rootb roota) ratc) (rat_mul (rat_add rata ratb) rootc) (rat_mul_undef (rat_add rootb roota) ratc (rat_add_undef rootb roota rootb_def_tmp))), have rootb_defined : (defined rootb), cc, clear rootb_def_tmp, by_cases rootc_def_tmp : (¬defined rootc), rw rat_mul_comm (rat_add rata ratb) rootc, exact undef_eq (rat_add (rat_mul rootc (rat_add rata ratb)) (rat_mul (rat_add roota rootb) ratc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul rootc (rat_add rata ratb)) (rat_mul (rat_add roota rootb) ratc) (rat_mul_undef rootc (rat_add rata ratb) rootc_def_tmp)), have rootc_defined : (defined rootc), cc, clear rootc_def_tmp, by_cases ratc_def_tmp : (¬defined ratc), rw rat_add_comm (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc), rw rat_mul_comm (rat_add roota rootb) ratc, exact undef_eq (rat_add (rat_mul ratc (rat_add roota rootb)) (rat_mul (rat_add rata ratb) rootc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul ratc (rat_add roota rootb)) (rat_mul (rat_add rata ratb) rootc) (rat_mul_undef ratc (rat_add roota rootb) ratc_def_tmp)), have ratc_defined : (defined ratc), cc, clear ratc_def_tmp, by_cases rata_def_tmp : (¬defined rata), exact undef_eq (rat_add (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc) (rat_mul_undef (rat_add rata ratb) rootc (rat_add_undef rata ratb rata_def_tmp))), have rata_defined : (defined rata), cc, clear rata_def_tmp, by_cases ratb_def_tmp : (¬defined ratb), rw rat_add_comm rata ratb, exact undef_eq (rat_add (rat_mul (rat_add ratb rata) rootc) (rat_mul (rat_add roota rootb) ratc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul (rat_add ratb rata) rootc) (rat_mul (rat_add roota rootb) ratc) (rat_mul_undef (rat_add ratb rata) rootc (rat_add_undef ratb rata ratb_def_tmp))), have ratb_defined : (defined ratb), cc, clear ratb_def_tmp, by_cases roota_def_tmp : (¬defined roota), rw rat_add_comm (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc), exact undef_eq (rat_add (rat_mul (rat_add roota rootb) ratc) (rat_mul (rat_add rata ratb) rootc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_undef (rat_mul (rat_add roota rootb) ratc) (rat_mul (rat_add rata ratb) rootc) (rat_mul_undef (rat_add roota rootb) ratc (rat_add_undef roota rootb roota_def_tmp))), have roota_defined : (defined roota), cc, clear roota_def_tmp,
    apply rat_eq_trans (rat_add (rat_mul (rat_add rata ratb) rootc) (rat_mul (rat_add roota rootb) ratc)) (rat_add (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) (rat_mul (rat_add roota rootb) ratc)) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_def (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) (rat_mul (rat_add roota rootb) ratc) ((rat_add_def (rat_mul rata rootc) (rat_mul ratb rootc) ((rat_mul_def rata rootc (rata_defined) (rootc_defined))) ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))))) ((rat_mul_def (rat_add roota rootb) ratc ((rat_add_def roota rootb (roota_defined) (rootb_defined))) (ratc_defined))))(add_eq_rat (rat_mul (rat_add rata ratb) rootc) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) (rat_mul (rat_add roota rootb) ratc) (rat_mul_distrib rata ratb rootc)), rw rat_add_comm (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) (rat_mul (rat_add roota rootb) ratc), apply rat_eq_trans (rat_add (rat_mul (rat_add roota rootb) ratc) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc))) (rat_add (rat_add (rat_mul roota ratc) (rat_mul rootb ratc)) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc))) (rat_add (rat_add (rat_add (rat_mul rata rootc) (rat_mul roota ratc)) (rat_mul ratb rootc)) (rat_mul rootb ratc)) (rat_add_def (rat_add (rat_mul roota ratc) (rat_mul rootb ratc)) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) ((rat_add_def (rat_mul roota ratc) (rat_mul rootb ratc) ((rat_mul_def roota ratc (roota_defined) (ratc_defined))) ((rat_mul_def rootb ratc (rootb_defined) (ratc_defined))))) ((rat_add_def (rat_mul rata rootc) (rat_mul ratb rootc) ((rat_mul_def rata rootc (rata_defined) (rootc_defined))) ((rat_mul_def ratb rootc (ratb_defined) (rootc_defined))))))(add_eq_rat (rat_mul (rat_add roota rootb) ratc) (rat_add (rat_mul roota ratc) (rat_mul rootb ratc)) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)) (rat_mul_distrib roota rootb ratc)),
    repeat {rw <- rat_add_assoc}, rw rat_add_comm (rat_mul rootb ratc) (rat_add (rat_mul rata rootc) (rat_mul ratb rootc)),
    repeat {rw rat_add_assoc}, rw rat_add_comm (rat_mul roota ratc) (rat_mul rata rootc),
    exact rat_eq_refl _,
end

/- TODO: Prove that multipliplying an rps by a rat still works as a multiplication by the field axioms.-/

def rat_four : myrat := (rat (int zero.mysucc.mysucc.mysucc.mysucc zero) (int zero.mysucc zero))

/- b^2 - 4ac -/
def discriminant : myrat -> myrat -> myrat -> myrat
| a b c := (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))

/- As this is of type (rat_plus_sqrt (discriminant a b c)) then it represents a number of the form
      x + y * sqrt (discriminant)
      The various occurrences of (discriminant a b c) make the formula more difficult to read, so a
      clearer presentaion would be
      mul_rps_by_rat (add_rps_to_rat (sqrt (discriminant) - b)) (reciprocal (a + a)
      Which is hopefully fairly obviously the well-known quadratic formula.-/
def quadratic_formula (a b c : myrat) : (rat_plus_sqrt (discriminant a b c)) :=
    mul_rps_by_rat (discriminant a b c)
      (add_rps_to_rat (discriminant a b c) (sqrt (discriminant a b c)) (negate_rat b))
      (rat_reciprocal (rat_add a a))

/- rat_plus_sqrt is a dependent type that takes a rat as argument.  -/
/- a + (b * sqrt(c)) is represented by the value (a,b) of type (rat_plus_sqrt c)-/

def quadratic_subst (k : myrat) : myrat -> myrat -> myrat -> (rat_plus_sqrt k) -> (rat_plus_sqrt k)
| a b c x := add_rps_to_rat k (add_rps k (mul_rps_by_rat k (mul_rps k x x) a) (mul_rps_by_rat k x b)) c

lemma half_defined : defined (rat_reciprocal rat_two) :=
begin
  unfold rat_two, unfold rat_reciprocal, unfold defined,
  apply mul_nonzero_int (int zero.mysucc.mysucc zero) int_one, unfold iszero, cc, unfold int_one,
  unfold nat_one, unfold iszero, cc,
end

lemma rat_two_defined : defined (rat_two) :=
begin
  unfold rat_two, unfold defined, unfold int_one, unfold iszero, unfold nat_one, cc,
end

lemma four_divided_by_two : rat_eq (rat_mul rat_four (rat_reciprocal rat_two)) rat_two :=
begin
  unfold rat_two, unfold rat_four, unfold rat_reciprocal, unfold rat_mul, unfold rat_eq, left,
  unfold int_one, unfold int_mul, unfold nat_one, repeat {unfold mymul}, repeat {rw zero_add}, repeat {rw add_zero},
  unfold mymul, unfold myadd, exact int_equal_refl _,
end

lemma add_two_halves (a : myrat) : rat_eq a (rat_add
                                                (rat_mul a (rat_reciprocal rat_two))
                                                (rat_mul a (rat_reciprocal rat_two))) :=
begin
  cases a with num den, unfold rat_two, unfold rat_reciprocal, unfold rat_mul,
  repeat {rw mul_one_int_rw},
  unfold rat_add, unfold rat_eq, left,
  rw mul_comm_int_rw den (int zero.mysucc.mysucc zero), rw mul_two_int den,
  repeat {rw mul_distrib_int_rw_alt}, repeat {rw mul_distrib_int_rw}, repeat {rw mul_distrib_int_rw_alt}, repeat {rw mul_distrib_int_rw},
  repeat {rw <- mul_assoc_int_rw den num den}, repeat {rw mul_comm_int_rw den num},
  repeat {rw mul_assoc_int_rw num den den}, repeat {rw add_assoc_int_rw},
  exact int_equal_refl _,
end

lemma mul_two_rat (a : myrat) : rat_eq (rat_mul a rat_two) (rat_add a a) :=
begin
  cases a with num den, unfold rat_two, unfold rat_mul,
  rw mul_comm_int_rw num (int zero.mysucc.mysucc zero), rw mul_two_int,
  unfold rat_add, unfold rat_eq, left, rw mul_one_int_rw, rw mul_distrib_int_rw,
  rw mul_comm_int_rw den (int_add (int_mul num den) (int_mul num den)), rw mul_distrib_int_rw,
  repeat {rw <- mul_assoc_int_rw}, exact int_equal_refl _,
end

lemma rat_zero_defined : defined (rat_zero) :=
begin
  unfold rat_zero, unfold defined, unfold int_one, unfold iszero, unfold nat_one, cc,
end

lemma quadratic_formula_works (a b c : myrat) :
  iszero_rps (discriminant a b c) (quadratic_subst (discriminant a b c) a b c (quadratic_formula a b c)) :=
begin
  /- As I have the intention of using a different approach for the cubic and quartic proofs, this
    is probably the swan-song of the python-generated code.  But Python is going to go out with
    a bang, I promise. ;-)
    -/
  unfold quadratic_subst, unfold quadratic_formula,
  unfold sqrt, unfold add_rps_to_rat,
  rw rat_add_comm rat_zero (negate_rat b), rw rat_add_zero_alt (negate_rat b),
  unfold mul_rps_by_rat, rw rat_mul_comm rat_one (rat_reciprocal (rat_add a a)),
  rw rat_mul_one_rw, unfold mul_rps, unfold mul_rps_by_rat,
  unfold add_rps, unfold add_rps_to_rat, unfold iszero_rps,
  split,
    unfold discriminant,
    by_cases a_def_tmp : (¬defined a), rw rat_mul_comm (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a, exact undef_iszero (rat_add (rat_add (rat_mul a (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_undef (rat_add (rat_mul a (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (rat_add_undef (rat_mul a (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_mul_undef a (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a_def_tmp))), have a_defined : (defined a), cc, clear a_def_tmp, by_cases c_def_tmp : (¬defined c), rw rat_add_comm (rat_add (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c, exact undef_iszero (rat_add c (rat_add (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b))) (rat_add_undef c (rat_add (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c_def_tmp), have c_defined : (defined c), cc, clear c_def_tmp, by_cases b_def_tmp : (¬defined b), rw rat_add_comm (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))), rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))), rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))), exact undef_iszero (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_undef (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_mul_undef (rat_add (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))))) a (rat_add_undef (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul_undef (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) (rat_mul_undef (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a)) (rat_add_undef (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul_undef b b b_def_tmp)))))))), have b_defined : (defined b), cc, clear b_def_tmp,
    have rat_four_defined : (defined rat_four), unfold rat_four, unfold defined, unfold iszero, cc,
    by_cases (iszero_rat a),
      have int1 : ¬defined (rat_reciprocal (rat_add a a)),
        apply reciprocal_zero_undef (rat_add a a),
        exact zeroes_only_eq_rat a (rat_add a a) a_defined (rat_eq_comm (rat_add a a) a (rat_add_zero a a h)) h,
      rw rat_mul_comm (negate_rat b) (rat_reciprocal (rat_add a a)),
      exact undef_iszero (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) b)) c) ((rat_add_undef (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) b)) c (rat_add_undef (rat_mul (rat_add (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) b) (rat_mul_undef (rat_add (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a (rat_add_undef (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) (rat_mul_undef (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat b)) (rat_mul_undef (rat_reciprocal (rat_add a a)) (negate_rat b) int1))))))),
      have int1 : defined (rat_reciprocal (rat_add a a)),
        exact reciprocal_def (rat_add a a) (rat_add_def a a a_defined a_defined) (add_self_nonzero_rat a h),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_def (rat_add (rat_add (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c ((rat_add_def (rat_add (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ((rat_add_def (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))) (int1) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (int1) ((rat_add_def (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))) ((rat_mul_def b b (b_defined) (b_defined))) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))))))))) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))))) (c_defined))(add_eq_rat (rat_add (rat_add (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (add_eq_rat (rat_add (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a)) (rat_mul (rat_add (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))))))) a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))))) a))))),
      rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))),
      rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))),
      rw rat_add_comm (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_def (rat_add (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c ((rat_add_def (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ((rat_add_def (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ((rat_mul_def (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a)) ((rat_add_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))))) (int1))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))))) (c_defined))(add_eq_rat (rat_add (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (add_eq_rat (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add (rat_mul (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (add_eq_rat (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (mul_eq_rat (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a (mul_eq_rat (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_add (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul b b) (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))))))))),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_def (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c ((rat_add_def (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ((rat_add_def (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ((rat_mul_def (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a ((rat_add_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))))) (c_defined))(add_eq_rat (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (add_eq_rat (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (add_eq_rat (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (mul_eq_rat (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) (rat_mul (rat_add (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a))) a ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))))))))),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add_def (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c ((rat_add_def (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ((rat_add_def (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ((rat_add_def (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) ((rat_mul_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))))) (c_defined))(add_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (add_eq_rat (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (add_eq_rat (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_add (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)))) a) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)))))),

      /- Multiply through by 2a.  As a ≠ 0 this doesn't affect the results of the iszero, but can make things easier.-/
      apply iszero_mul_rat (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add a a) (add_self_nonzero_rat a h) (rat_add_def a a a_defined a_defined),

      /- Now we do a lot of work to cancel the 2a and the 1/2a in every term where they both appear.-/
      apply zeroes_only_eq_rat (rat_add (rat_mul (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add a a)) (rat_mul c (rat_add a a))) (rat_mul (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c) (rat_add a a)) (rat_add_def (rat_mul (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add a a)) (rat_mul c (rat_add a a)) ((rat_mul_def (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add a a) ((rat_add_def (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) ((rat_add_def (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ((rat_add_def (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) ((rat_mul_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))( (rat_eq_comm _ _ (rat_mul_distrib (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) c (rat_add a a)))),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_mul (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add a a)) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_mul_def (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a) ((rat_add_def (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) ((rat_add_def (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) ((rat_mul_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b)) (rat_add a a)) (rat_mul c (rat_add a a)) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))))),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_add_def (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) ((rat_mul_def (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a) ((rat_add_def (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) ((rat_mul_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) (a_defined))) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_add (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))))),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_add_def (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) ((rat_add_def (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) ((rat_mul_def (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (rat_mul b b) (rat_reciprocal (rat_add a a)) ((rat_mul_def b b (b_defined) (b_defined))) (int1))) (int1))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_add (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_add (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) (add_eq_rat (rat_add (rat_mul (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_add (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))))))),
      rw rat_mul_comm (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a, rw rat_mul_comm (rat_add a a) (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_add a a)) a, rw rat_mul_comm (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_add a a)) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_mul b b) (rat_reciprocal (rat_add a a))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul b b) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (rat_mul b b), rw rat_mul_assoc (rat_mul b b) (rat_add a a) (rat_reciprocal (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_add_def (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) ((rat_add_def (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a ((rat_mul_def (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)) ((rat_mul_def (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))) (int1))) (int1))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) (add_eq_rat (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) (add_eq_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)) (mul_eq_rat_alt (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) a (mul_eq_rat_alt (rat_mul b b) (rat_mul (rat_mul b b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a)) (reciprocal_mul_cancel (rat_mul b b) (rat_add a a)))))))),
      rw rat_add_comm (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a)),
      rw rat_mul_comm (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) a, rw rat_mul_comm (rat_add a a) (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_add a a)) a, rw rat_mul_comm (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_add a a)) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (negate_rat (rat_mul rat_four (rat_mul a c))), rw rat_mul_assoc (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_add a a) (rat_reciprocal (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_add_def (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) ((rat_add_def (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c)))) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))) (int1) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))))))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))))) ((rat_mul_def (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_add (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) (add_eq_rat (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) (add_eq_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (mul_eq_rat_alt (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c)))) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) a (mul_eq_rat_alt (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) (rat_reciprocal (rat_add a a)) (reciprocal_mul_cancel (negate_rat (rat_mul rat_four (rat_mul a c))) (rat_add a a)))))))),
      rw rat_add_comm (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a)),
      rw rat_mul_comm (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) a, rw rat_mul_comm (rat_add a a) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))), rw rat_mul_comm (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_add a a)) a, rw rat_mul_comm (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a)))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_add a a) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_add a a)) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (negate_rat b) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (negate_rat b), rw rat_mul_assoc (negate_rat b) (rat_add a a) (rat_reciprocal (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) ((rat_add_def (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) ((rat_mul_def a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b)) (a_defined) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b) ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) ((negate_def b b_defined)))))) ((rat_add_def (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c)))) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))) (int1) ((negate_def (rat_mul rat_four (rat_mul a c)) (rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))))))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))))))) ((rat_mul_def (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a) ((rat_mul_def (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b ((rat_mul_def (negate_rat b) (rat_reciprocal (rat_add a a)) ((negate_def b b_defined)) (int1))) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_add (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_add (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) b) (rat_add a a)) (add_eq_rat (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b))) (rat_mul a (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (mul_eq_rat_alt (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (negate_rat b)) (rat_mul (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) a (mul_eq_rat_alt (negate_rat b) (rat_mul (negate_rat b) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) (rat_mul (negate_rat b) (rat_reciprocal (rat_add a a))) (reciprocal_mul_cancel (negate_rat b) (rat_add a a))))))),
      repeat {rw mul_negate_alt_rw},
      rw rat_add_comm (rat_add (rat_mul a (rat_mul (rat_mul b (negate_rat (rat_reciprocal (rat_add a a)))) (negate_rat b))) (rat_add (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (negate_rat (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_mul (rat_mul (rat_mul b (negate_rat (rat_reciprocal (rat_add a a)))) b) (rat_add a a)),
      repeat {rw rat_mul_assoc}, repeat {rw mul_negate_rw}, repeat {rw mul_negate_alt_rw}, repeat {rw mul_negate_rw},
      rw double_negate,
      rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_mul b (rat_add a a)), rw rat_mul_assoc b (rat_add a a) (rat_reciprocal (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add (rat_add (negate_rat (rat_mul b b)) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))))) (rat_mul c (rat_add a a))) (rat_add (rat_add (negate_rat (rat_mul b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (negate_rat (rat_mul b b)) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))))) (rat_mul c (rat_add a a)) ((rat_add_def (negate_rat (rat_mul b b)) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) ((negate_def (rat_mul b b) (rat_mul_def b b (b_defined) (b_defined)))) ((rat_add_def (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) ((rat_mul_def a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b)) (a_defined) ((rat_mul_def b (rat_mul (rat_reciprocal (rat_add a a)) b) (b_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))))))) ((rat_add_def (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) ((negate_def (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c)))) (rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c)) (int1) ((rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))))))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (negate_rat (rat_mul b b)) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))))) (rat_add (negate_rat (rat_mul b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))))) (rat_mul c (rat_add a a)) (add_eq_rat (negate_rat (rat_mul b b)) (negate_rat (rat_mul b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_eq_rat (rat_mul b b) (rat_mul b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) (mul_eq_rat_alt b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) b (reciprocal_mul_cancel b (rat_add a a)))))),

      /- Now we have two locations with a * 1/(a + a), so we can cancel them down to 1/2  -/
      rw rat_add_comm (negate_rat (rat_mul b b)) (rat_add (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) b))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))), repeat {rw rat_mul_assoc},
      rw <- rat_mul_assoc a b (rat_mul (rat_reciprocal (rat_add a a)) b), rw rat_mul_comm a b, rw rat_mul_assoc b a (rat_mul (rat_reciprocal (rat_add a a)) b), rw <- rat_mul_assoc a (rat_reciprocal (rat_add a a)) b, rw rat_mul_comm a (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) a) b, rw rat_mul_comm (rat_reciprocal (rat_add a a)) a,
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_mul b (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b)) ((rat_add_def (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) ((rat_mul_def b (rat_mul b (rat_reciprocal rat_two)) (b_defined) ((rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined))))) ((rat_add_def (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) ((negate_def (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c)))) (rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c)) (int1) ((rat_mul_def rat_four (rat_mul a c) (rat_four_defined) ((rat_mul_def a c (a_defined) (c_defined)))))))))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))))))) ((negate_def (rat_mul b b) (rat_mul_def b b (b_defined) (b_defined)))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b))) (rat_add (rat_add (rat_mul b (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (rat_add (rat_mul b (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))))) (negate_rat (rat_mul b b)) (add_eq_rat (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_mul b (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (mul_eq_rat_alt (rat_mul b (rat_reciprocal rat_two)) (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a)))) b (mul_eq_rat_alt (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) b (half_reciprocal_mul a)))))),
      rw rat_add_comm (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))),
      rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_mul rat_four (rat_mul a c)), rw rat_mul_assoc rat_four (rat_mul a c) (rat_reciprocal (rat_add a a)), rw rat_mul_assoc a c (rat_reciprocal (rat_add a a)), rw <- rat_mul_assoc a c (rat_reciprocal (rat_add a a)), rw rat_mul_comm a c, rw rat_mul_assoc c a (rat_reciprocal (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b)) ((rat_add_def (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two))) ((rat_add_def (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) ((negate_def (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))) (rat_mul_def a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))) (a_defined) ((rat_mul_def rat_four (rat_mul c (rat_reciprocal rat_two)) (rat_four_defined) ((rat_mul_def c (rat_reciprocal rat_two) (c_defined) (half_defined)))))))) ((rat_mul_def a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)) (a_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b b) (int1) ((rat_mul_def b b (b_defined) (b_defined))))))))) ((rat_mul_def b (rat_mul b (rat_reciprocal rat_two)) (b_defined) ((rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined))))))) ((negate_def (rat_mul b b) (rat_mul_def b b (b_defined) (b_defined)))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_add (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b)) (add_eq_rat (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b)))) (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (add_eq_rat (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))))) (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))) (negate_eq_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))) (rat_mul a (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a)))))) (mul_eq_rat_alt (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))) (rat_mul rat_four (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a))))) a (mul_eq_rat_alt (rat_mul c (rat_reciprocal rat_two)) (rat_mul c (rat_mul a (rat_reciprocal (rat_add a a)))) rat_four (mul_eq_rat_alt (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) c (half_reciprocal_mul a))))))))),
      rw rat_add_comm (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))  (rat_mul a (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b b))),
      rw <- rat_mul_assoc a (rat_reciprocal (rat_add a a)) (rat_mul b b), rw rat_mul_comm a (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) a) (rat_mul b b), rw rat_mul_comm (rat_reciprocal (rat_add a a)) a,
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add (rat_add (rat_add (rat_add (rat_mul (rat_mul b b) (rat_mul a (rat_reciprocal (rat_add a a)))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (rat_add_def (rat_add (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) ((rat_add_def (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b)) ((rat_add_def (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two))) ((rat_add_def (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) ((rat_mul_def (rat_mul b b) (rat_reciprocal rat_two) ((rat_mul_def b b (b_defined) (b_defined))) (half_defined))) ((negate_def (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))) (rat_mul_def a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))) (a_defined) ((rat_mul_def rat_four (rat_mul c (rat_reciprocal rat_two)) (rat_four_defined) ((rat_mul_def c (rat_reciprocal rat_two) (c_defined) (half_defined)))))))))) ((rat_mul_def b (rat_mul b (rat_reciprocal rat_two)) (b_defined) ((rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined))))))) ((negate_def (rat_mul b b) (rat_mul_def b b (b_defined) (b_defined)))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_add (rat_add (rat_add (rat_mul (rat_mul b b) (rat_mul a (rat_reciprocal (rat_add a a)))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) (add_eq_rat (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (rat_add (rat_add (rat_mul (rat_mul b b) (rat_mul a (rat_reciprocal (rat_add a a)))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two)))) (negate_rat (rat_mul b b)) (add_eq_rat (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_add (rat_mul (rat_mul b b) (rat_mul a (rat_reciprocal (rat_add a a)))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two))) (add_eq_rat (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (rat_mul (rat_mul b b) (rat_mul a (rat_reciprocal (rat_add a a)))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (mul_eq_rat_alt (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) (rat_mul b b) (half_reciprocal_mul a)))))),

      /- Now we have two terms of the form ((b^2) * 1/2) -/
      /- We can add them together to make a single b^2 term-/
      rw rat_add_comm (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))))) (rat_mul b (rat_mul b (rat_reciprocal rat_two))), repeat {rw rat_add_assoc},
      repeat {rw <- rat_mul_assoc b b (rat_reciprocal rat_two)},
      repeat {rw <- rat_add_assoc (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (rat_mul (rat_mul b b) (rat_reciprocal rat_two))) _ _},
      apply zeroes_only_eq_rat (rat_add (rat_mul b b) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)))) (rat_add (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (rat_mul (rat_mul b b) (rat_reciprocal rat_two))) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)))) (rat_add_def (rat_mul b b) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) ((rat_mul_def b b (b_defined) (b_defined))) ((rat_add_def (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a)) ((rat_add_def (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b)) ((negate_def (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))) (rat_mul_def a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))) (a_defined) ((rat_mul_def rat_four (rat_mul c (rat_reciprocal rat_two)) (rat_four_defined) ((rat_mul_def c (rat_reciprocal rat_two) (c_defined) (half_defined)))))))) ((negate_def (rat_mul b b) (rat_mul_def b b (b_defined) (b_defined)))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined)))))))) (add_eq_rat (rat_mul b b) (rat_add (rat_mul (rat_mul b b) (rat_reciprocal rat_two)) (rat_mul (rat_mul b b) (rat_reciprocal rat_two))) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b))) (rat_mul c (rat_add a a))) (add_two_halves (rat_mul b b))),

      /- And now we have both b^2 and -(b^2), so we can cancel them.-/
      rw rat_add_comm (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (negate_rat (rat_mul b b)),
      repeat {rw rat_add_assoc (rat_mul b b) _ _},  rw <- rat_add_assoc (rat_add (rat_mul b b) (negate_rat (rat_mul b b))) (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a)),
      apply zeroes_only_eq_rat (rat_add rat_zero (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a))))  (rat_add (rat_add (rat_mul b b) (negate_rat (rat_mul b b))) (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a)))) (rat_add_def rat_zero (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a))) (rat_zero_defined) ((rat_add_def (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a)) ((negate_def (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two)))) (rat_mul_def a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))) (a_defined) ((rat_mul_def rat_four (rat_mul c (rat_reciprocal rat_two)) (rat_four_defined) ((rat_mul_def c (rat_reciprocal rat_two) (c_defined) (half_defined)))))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined)))))))) (add_eq_rat rat_zero (rat_add (rat_mul b b) (negate_rat (rat_mul b b))) (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a))) (rat_eq_comm (rat_add (rat_mul b b) (negate_rat (rat_mul b b))) rat_zero (add_negate_rat (rat_mul b b)))),
      rw rat_add_comm rat_zero (rat_add (negate_rat (rat_mul a (rat_mul rat_four (rat_mul c (rat_reciprocal rat_two))))) (rat_mul c (rat_add a a))),
      rw rat_add_zero_alt,

      /- We have eliminated all the terms with b in them, all that's left is
        -4ac/2 + c(a + a) = 0.  Not much left to do, first cancel the 4/2-/
      rw <- rat_mul_assoc rat_four c (rat_reciprocal rat_two), rw rat_mul_comm rat_four c,
      rw rat_mul_comm a (rat_mul (rat_mul c rat_four) (rat_reciprocal rat_two)),
      rw rat_mul_assoc c rat_four (rat_reciprocal rat_two), rw rat_mul_comm c (rat_mul rat_four (rat_reciprocal rat_two)),
      rw rat_mul_assoc (rat_mul rat_four (rat_reciprocal rat_two)) c a,
      apply zeroes_only_eq_rat (rat_add (negate_rat (rat_mul rat_two (rat_mul c a))) (rat_mul c (rat_add a a))) (rat_add (negate_rat (rat_mul (rat_mul rat_four (rat_reciprocal rat_two)) (rat_mul c a))) (rat_mul c (rat_add a a))) (rat_add_def (negate_rat (rat_mul rat_two (rat_mul c a))) (rat_mul c (rat_add a a)) ((negate_def (rat_mul rat_two (rat_mul c a)) (rat_mul_def rat_two (rat_mul c a) (rat_two_defined) ((rat_mul_def c a (c_defined) (a_defined)))))) ((rat_mul_def c (rat_add a a) (c_defined) ((rat_add_def a a (a_defined) (a_defined)))))) (add_eq_rat (negate_rat (rat_mul rat_two (rat_mul c a))) (negate_rat (rat_mul (rat_mul rat_four (rat_reciprocal rat_two)) (rat_mul c a))) (rat_mul c (rat_add a a)) (negate_eq_rat (rat_mul rat_two (rat_mul c a)) (rat_mul (rat_mul rat_four (rat_reciprocal rat_two)) (rat_mul c a)) (mul_eq_rat rat_two (rat_mul rat_four (rat_reciprocal rat_two)) (rat_mul c a) (rat_eq_comm (rat_mul rat_four (rat_reciprocal rat_two)) rat_two four_divided_by_two)))),

     /- And finally, just prove that 2ca = c(a + a)-/
      rw rat_add_comm (negate_rat (rat_mul rat_two (rat_mul c a))) (rat_mul c (rat_add a a)),
      rw rat_mul_comm c (rat_add a a),
      apply zeroes_only_eq_rat (rat_add (rat_mul (rat_mul a rat_two) c) (negate_rat (rat_mul rat_two (rat_mul c a)))) (rat_add (rat_mul (rat_add a a) c) (negate_rat (rat_mul rat_two (rat_mul c a)))) (rat_add_def (rat_mul (rat_mul a rat_two) c) (negate_rat (rat_mul rat_two (rat_mul c a))) ((rat_mul_def (rat_mul a rat_two) c ((rat_mul_def a rat_two (a_defined) (rat_two_defined))) (c_defined))) ((negate_def (rat_mul rat_two (rat_mul c a)) (rat_mul_def rat_two (rat_mul c a) (rat_two_defined) ((rat_mul_def c a (c_defined) (a_defined))))))) (add_eq_rat (rat_mul (rat_mul a rat_two) c) (rat_mul (rat_add a a) c) (negate_rat (rat_mul rat_two (rat_mul c a))) (mul_eq_rat (rat_mul a rat_two) (rat_add a a) c (mul_two_rat a))),
      rw rat_mul_comm c a, rw rat_mul_comm a rat_two, rw rat_mul_assoc,
      exact add_negate_rat_alt (rat_mul rat_two (rat_mul a c)),

      /- And we are DONE for the first goal (the part that isn't multiplied by the root of the discriminant)! -/
      /- For the second goal, start by again doing all the trivial cases with undefined values, yay Python.-/
      by_cases a_def_tmp : (¬defined a), rw rat_mul_comm (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a, exact undef_iszero (rat_add (rat_mul a (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))))) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add_undef (rat_mul a (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))))) (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_mul_undef a (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a_def_tmp)), have a_defined : (defined a), cc, clear a_def_tmp, by_cases b_def_tmp : (¬defined b), exact undef_iszero (rat_add (rat_mul (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add_undef (rat_mul (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_mul_undef (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a (rat_add_undef (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_undef (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_mul_undef b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b_def_tmp))))), have b_defined : (defined b), cc, clear b_def_tmp,
      by_cases recip_def_tmp : (¬defined (rat_reciprocal (rat_add a a))), rw rat_mul_comm b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))),
      exact undef_iszero (rat_add (rat_mul (rat_add (negate_rat (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b)) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add_undef (rat_mul (rat_add (negate_rat (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b)) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_mul_undef (rat_add (negate_rat (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b)) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a (rat_add_undef (negate_rat (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b)) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_undef (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b) (rat_mul_undef (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) b (rat_mul_undef (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)) recip_def_tmp)))))), have int1 : defined (rat_reciprocal (rat_add a a)), cc, clear recip_def_tmp,
      have h : (¬iszero_rat a), intro h, exact reciprocal_zero_undef (rat_add a a) (zeroes_only_eq_rat a (rat_add a a) a_defined (rat_eq_comm (rat_add a a) a (rat_add_zero a a h)) h) int1,

      /- Now do the distributive rewrite.-/
      apply zeroes_only_eq_rat (rat_add (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add (rat_mul (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add_def (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_reciprocal (rat_add a a)) b) ((rat_add_def (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) ((rat_mul_def (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_mul_def b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) (b_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)) (int1) (int1)))))) (a_defined))) ((rat_mul_def (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))) (int1) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) (a_defined))))) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))))(add_eq_rat (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_add (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))))) a) (rat_mul (rat_reciprocal (rat_add a a)) b) ( (rat_eq_comm _ _ (rat_mul_distrib (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)))),

      /- Again. multiply through by 2a.-/
      apply iszero_mul_rat (rat_add (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add a a) (add_self_nonzero_rat a h) (rat_add_def a a a_defined a_defined),
      apply zeroes_only_eq_rat (rat_add (rat_mul (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_mul (rat_add (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_reciprocal (rat_add a a)) b)) (rat_add a a)) (rat_add_def (rat_mul (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) ((rat_mul_def (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_add a a) ((rat_add_def (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) ((rat_mul_def (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_mul_def b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) (b_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)) (int1) (int1)))))) (a_defined))) ((rat_mul_def (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))) (int1) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) (a_defined))))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))( (rat_eq_comm _ _ (rat_mul_distrib (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)))), apply zeroes_only_eq_rat (rat_add (rat_add (rat_mul (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_add a a)) (rat_mul (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add (rat_mul (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add_def (rat_add (rat_mul (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_add a a)) (rat_mul (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) ((rat_add_def (rat_mul (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_add a a)) (rat_mul (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a)) ((rat_mul_def (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_add a a) ((rat_mul_def (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_mul_def b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))) (b_defined) ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)) (int1) (int1)))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))) ((rat_mul_def (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a) ((rat_mul_def (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a ((negate_def (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))) (int1) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined))))))) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (rat_mul (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_add a a)) (rat_mul (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a))) (rat_mul (rat_add (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a)) (rat_add a a)) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) ( (rat_eq_comm _ _ (rat_mul_distrib (rat_mul (negate_rat (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))))) a) (rat_mul (negate_rat (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))))) a) (rat_add a a))))),
      repeat {rw mul_negate_alt_rw}, repeat {rw mul_negate_rw}, repeat {rw mul_negate_alt_rw}, repeat {rw mul_negate_rw},


      /- Cancel where possible (which is everywhere for this bit).-/
      rw rat_mul_comm (rat_mul (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) a) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) a, rw rat_mul_comm (rat_add a a) (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))), rw rat_mul_comm (rat_mul (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_add a a)) a, rw rat_mul_comm (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) b (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_add a a) b, rw rat_mul_assoc b (rat_add a a) (rat_mul (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a))), rw <- rat_mul_assoc (rat_add a a) (rat_reciprocal (rat_add a a)) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_add a a) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) (rat_add a a)) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_add a a),
      apply zeroes_only_eq_rat (rat_add (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add_def (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) ((rat_add_def (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) ((negate_def (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def a (rat_mul b (rat_reciprocal (rat_add a a))) (a_defined) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) ((negate_def (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)) (rat_mul_def (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a ((rat_mul_def (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))) (int1) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1))))) (a_defined))) ((rat_add_def a a (a_defined) (a_defined)))))))) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))) (rat_add (negate_rat (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a)))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) (add_eq_rat (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a))) (negate_eq_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul a (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (mul_eq_rat_alt (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul b (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) a (mul_eq_rat_alt (rat_reciprocal (rat_add a a)) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) b (reciprocal_mul_cancel (rat_reciprocal (rat_add a a)) (rat_add a a))))))),
      rw rat_add_comm (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a))),
      rw rat_mul_comm (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) a, rw rat_mul_comm (rat_add a a) (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))), rw rat_mul_comm (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_add a a)) a, rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_reciprocal (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_add a a) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) (rat_add a a)) (rat_mul b (rat_reciprocal (rat_add a a))), rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_add a a),
      apply zeroes_only_eq_rat (rat_add (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add (rat_add (negate_rat (rat_mul a (rat_mul (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a))) (rat_add_def (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) ((rat_add_def (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) ((negate_def (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def a (rat_mul b (rat_reciprocal (rat_add a a))) (a_defined) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) ((negate_def (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def a (rat_mul b (rat_reciprocal (rat_add a a))) (a_defined) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))))) ((rat_mul_def (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a) ((rat_mul_def (rat_reciprocal (rat_add a a)) b (int1) (b_defined))) ((rat_add_def a a (a_defined) (a_defined))))))(add_eq_rat (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_add (negate_rat (rat_mul a (rat_mul (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)) (add_eq_rat (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_eq_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul a (rat_mul (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a))))) (mul_eq_rat_alt (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_mul b (rat_reciprocal (rat_add a a))) (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) a (reciprocal_mul_cancel (rat_mul b (rat_reciprocal (rat_add a a))) (rat_add a a)))))),
      rw rat_add_comm (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (rat_mul (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a)),
      rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) b) (rat_add a a), rw <- rat_mul_assoc (rat_add a a) (rat_reciprocal (rat_add a a)) b, rw rat_mul_comm (rat_add a a) (rat_reciprocal (rat_add a a)), rw rat_mul_comm (rat_mul (rat_reciprocal (rat_add a a)) (rat_add a a)) b, rw rat_mul_comm (rat_reciprocal (rat_add a a)) (rat_add a a),
      apply zeroes_only_eq_rat (rat_add b (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))))) (rat_add (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))))) (rat_add_def b (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) b_defined ((rat_add_def (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) ((negate_def (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def a (rat_mul b (rat_reciprocal (rat_add a a))) (a_defined) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1)))))) ((negate_def (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))) (rat_mul_def a (rat_mul b (rat_reciprocal (rat_add a a))) (a_defined) ((rat_mul_def b (rat_reciprocal (rat_add a a)) (b_defined) (int1))))))))) (add_eq_rat b (rat_mul b (rat_mul (rat_add a a) (rat_reciprocal (rat_add a a)))) (rat_add (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a))))) (negate_rat (rat_mul a (rat_mul b (rat_reciprocal (rat_add a a)))))) (reciprocal_mul_cancel b (rat_add a a))),

      /- Cancel in the two nodes that have a * 1/(a + a)-/
      rw rat_add_comm b _, rw rat_mul_comm b (rat_reciprocal (rat_add a a)),
      rw <- rat_mul_assoc a (rat_reciprocal (rat_add a a)) b, rw <- rat_add_assoc,
      rw rat_mul_comm (rat_mul a (rat_reciprocal (rat_add a a))) b,
      apply zeroes_only_eq_rat (rat_add (negate_rat (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b)) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b)) (rat_add_def (negate_rat (rat_mul b (rat_reciprocal rat_two))) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b) ((negate_def (rat_mul b (rat_reciprocal rat_two)) (rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined)))) ((rat_add_def (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b ((negate_def (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a)))) (rat_mul_def b (rat_mul a (rat_reciprocal (rat_add a a))) (b_defined) ((rat_mul_def a (rat_reciprocal (rat_add a a)) (a_defined) (int1)))))) (b_defined))))(add_eq_rat (negate_rat (rat_mul b (rat_reciprocal rat_two))) (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b) (negate_eq_rat (rat_mul b (rat_reciprocal rat_two)) (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a)))) (mul_eq_rat_alt (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) b (half_reciprocal_mul a)))),
      rw rat_add_comm,
      apply zeroes_only_eq_rat (rat_add (rat_add (negate_rat (rat_mul b (rat_reciprocal rat_two))) b) (negate_rat (rat_mul b (rat_reciprocal rat_two)))) (rat_add (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b) (negate_rat (rat_mul b (rat_reciprocal rat_two)))) (rat_add_def (rat_add (negate_rat (rat_mul b (rat_reciprocal rat_two))) b) (negate_rat (rat_mul b (rat_reciprocal rat_two))) ((rat_add_def (negate_rat (rat_mul b (rat_reciprocal rat_two))) b ((negate_def (rat_mul b (rat_reciprocal rat_two)) (rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined)))) (b_defined))) ((negate_def (rat_mul b (rat_reciprocal rat_two)) (rat_mul_def b (rat_reciprocal rat_two) (b_defined) (half_defined)))))(add_eq_rat (rat_add (negate_rat (rat_mul b (rat_reciprocal rat_two))) b) (rat_add (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b) (negate_rat (rat_mul b (rat_reciprocal rat_two))) (add_eq_rat (negate_rat (rat_mul b (rat_reciprocal rat_two))) (negate_rat (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a))))) b (negate_eq_rat (rat_mul b (rat_reciprocal rat_two)) (rat_mul b (rat_mul a (rat_reciprocal (rat_add a a)))) (mul_eq_rat_alt (rat_reciprocal rat_two) (rat_mul a (rat_reciprocal (rat_add a a))) b (half_reciprocal_mul a))))),

      /- Add the two -b/2 terms together...-/
      rw rat_mul_comm b (rat_reciprocal rat_two), rw <- mul_negate_rw (rat_reciprocal rat_two) b, rw rat_mul_comm (rat_reciprocal rat_two) (negate_rat b),
      rw rat_add_comm (rat_mul (negate_rat b) (rat_reciprocal rat_two)) b, rw <- rat_add_assoc, rw rat_add_comm,
      apply zeroes_only_eq_rat (rat_add (negate_rat b) b) (rat_add (rat_add (rat_mul (negate_rat b) (rat_reciprocal rat_two)) (rat_mul (negate_rat b) (rat_reciprocal rat_two))) b) (rat_add_def (negate_rat b) b ((negate_def b b_defined)) (b_defined)) (add_eq_rat (negate_rat b) (rat_add (rat_mul (negate_rat b) (rat_reciprocal rat_two)) (rat_mul (negate_rat b) (rat_reciprocal rat_two))) b (add_two_halves (negate_rat b))),

      /- And all we have left is (-b) + b, which is obviously zero.-/
      rw rat_add_comm,
      exact add_negate_rat_alt b,
      /- QUOD.-/
      /- ERAT.-/
      /- DEMONSTRANDUM.-/

end

