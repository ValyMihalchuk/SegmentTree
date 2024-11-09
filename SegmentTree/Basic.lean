import SegmentTree



structure segmentTree where
  l   : List ℕ -- tree as list
  orig_size : ℕ -- original size of array



inductive proper (st : segmentTree) : Prop where
  | intro
    (h1 : st.orig_size > 0)
    (h2: st.l.length = 2 * st.orig_size - 1)
    (h3:  ∀i, (hh : i < st.orig_size - 1)
   -> st.l[i] =  st.l[2*i+1] +
   st.l[2*i+2]) : proper st



lemma proper_len_eq_2orig_size_minus_one (st : segmentTree) (hv: proper st) : st.l.length  = 2*st.orig_size-1 :=
by
  cases hv with
  | intro hh1 hh2 hh3 =>
      omega

lemma proper_orig_size_eq_half_len (st : segmentTree) (hv: proper st) : st.l.length / 2 = st.orig_size-1 :=
by
  cases hv with
  | intro hh1 hh2 hh3 =>
      omega

lemma proper_orig_size_index_lt_len (st : segmentTree) (hp : proper st) :
∀ i, i < st.orig_size -> i + st.orig_size - 1 < st.l.length :=
by
  intro i hi
  cases hp with
  | intro h1 h2 h3 => omega

lemma proper_n_plus_half_len_lt_len (st : segmentTree) (n :ℕ) (h : n < st.orig_size) (hv: proper st) : st.l.length / 2 + n < st.l.length :=
by
  cases hv with
  | intro hh1 hh2 hh3 =>
    omega

lemma  proper_n_plus_half_len_gt_orig_size (st : segmentTree) (n:ℕ) (h: proper st) :  st.l.length / 2 + n >= st.orig_size - 1 :=
by
  cases h with
  | intro h1 h2 h3 => omega

lemma proper_i_lt_orig_size_minus_one_lt_len (st : segmentTree) (hp : proper st) :
∀ i, i < st.orig_size - 1 -> i < st.l.length :=
by
  intro i hi
  cases hp with
  | intro h1 h2 h3 => omega


lemma proper_2i_1_lt_orig_size_minus_one_lt_len (st : segmentTree) (hp : proper st) :
∀ i, i < st.orig_size - 1 -> 2*i+1 < st.l.length :=
by
  intro i hi
  cases hp with
  | intro h1 h2 h3 => omega

lemma proper_2i_2_lt_orig_size_minus_one_lt_len (st : segmentTree) (hp : proper st) :
∀ i, i < st.orig_size - 1 -> 2*i + 2 < st.l.length :=
by
  intro i hi
  cases hp with
  | intro h1 h2 h3 => omega

macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simp[proper_n_plus_half_len_lt_len])

def sum (l: List ℕ) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= l.length): ℕ :=
 if h1 : a = b then 0 else
 l[a]  + sum l (a+1) b (by omega) hb
 termination_by (b-a)

lemma sum_cut_one_left (l:List ℕ)  (a b : ℕ) (hab: a < b) (h : b ≤ l.length) :
sum l a b (by omega) (by omega)= l[a] + sum l (a+1) b (by omega) (by omega) :=
 by
  have m : ¬(a=b) := by omega
  rw[sum]
  simp[m]


lemma sum_cut_one_right (l: List ℕ) (a : ℕ) (b : ℕ) (h: a<b) (hb : b <= l.length):
sum l a b (by omega) hb = sum l a (b-1) (by omega) (by omega) + l[b-1]'(by omega) :=
 if heq : a = b then
  show _ from
  by
    have m: ¬(a=b) := by omega
    simp [heq] at m
 else
  show _ from
  by
    cases Classical.em (b=a+1) with
    | inl hba => simp[hba,sum]
    | inr hba =>
      simp[sum_cut_one_left l a b h hb, sum_cut_one_left l a (b-1) (by omega) (by omega),
      sum_cut_one_right l (a+1) b (by omega) (by omega)]
      ac_rfl


lemma sum_cut_two_left (st :segmentTree)  (a b : ℕ) (hab: a < b)
 (hb: 2*b < st.l.length ) : sum st.l (2*a+1) (2*b+1) (by omega) (by omega) =
 st.l[2*a+1]+st.l[2*a+2] + sum st.l (2*a+3) (2*b+1) (by omega) (by omega) :=
 by
  cases Classical.em (b=a+1) with
  | inl h =>
    simp [h, (by omega : ∀ a, 2*(a+1)+1 = 2*a+3), sum]
  | inr h =>
    have m : ¬(2*a+1=2*b+1) := by omega
    rw[sum]
    simp[m]
    nth_rewrite 1 [sum]
    have mm : ¬(2 * a + 1 + 1 = 2 * b + 1) := by omega
    simp[mm, (by omega : ∀ a, 2*a+1+1 = 2*a+2), (by omega : ∀ a, 2*a+2+1 = 2*a+3)]
    ac_rfl



def get_ (st :segmentTree) : List ℕ :=  List.drop (st.orig_size-1) st.l
def my_get (st :segmentTree) (i : ℕ) (h: i+st.orig_size-1 < st.l.length) : ℕ :=
 st.l[i+st.orig_size-1]


def my_sum (st :segmentTree)  (a : ℕ) (b : ℕ) (h: a≤b) (hb: b+st.orig_size-1 ≤ st.l.length)
(hl : st.orig_size > 0) : ℕ :=
 if h1 : a = b then 0 else
 my_get st a (by omega)  + my_sum st (a+1) b (by omega) hb hl
 termination_by (b-a)

lemma my_sum_sum  (st :segmentTree)  (a : ℕ) (b : ℕ) (h: a≤b)
(hb: b+st.orig_size-1 ≤ st.l.length) (hl : st.orig_size > 0):
sum st.l (a+st.orig_size-1) (b+st.orig_size-1) (by omega) hb
= my_sum st a b h hb hl :=
if heq : a = b then
  show _ from
  by
    simp [heq, sum, my_sum]
 else
  show _ from
  by
    rw[sum, my_sum]
    have m : ¬(a + st.orig_size - 1 = b + st.orig_size - 1) := by omega
    have mm : ¬(a=b) := by omega
    simp[m, mm, my_get,
    (by omega: a + st.orig_size - 1 + 1 = a + st.orig_size),
    ←my_sum_sum  st (a+1) b (by omega) hb hl]



def init (n : ℕ) : segmentTree :=
 { l := List.replicate (2*n-1) 0
   orig_size := n }


theorem init_correctness (result : segmentTree) (n : ℕ) (h : 0 < n) :
   (h1: result = init n) → (proper result ∧ n = result.orig_size) ∧
   ∀ i, (h2: i < n) -> my_get result i (by simp[init, h1]; omega) = 0 :=
by
  intro hres
  apply And.intro
  { apply And.intro
    { apply proper.intro <;>
       simp[hres, init, h] }
    { simp[hres, init] }}
  { simp[hres, init, List.replicate, my_get] }




def add'_list (l : List ℕ) (x:ℕ) (n : ℕ) (h : n < l.length) : List ℕ :=
match n with
| 0 => l
| n+1 => (add'_list l x (n/2) (by omega)).set (n/2) (x+l[n/2])



lemma len_add'_list (l : List ℕ) (x:ℕ) (n : ℕ) (h : n < l.length) :
(add'_list l x n h).length = l.length :=
by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases n with
    | zero => simp[add'_list]
    | succ n' =>
      simp [add'_list]
      apply ih
      apply Nat.div_lt_of_lt_mul
      linarith

macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simp[len_add'_list]; assumption)



lemma add'_list_eq_strong (l : List ℕ) (x:ℕ) (n : ℕ) (h : n < l.length) (i:ℕ) (hi: i > (n-1)/2)
(hii : i  < l.length ) :
(add'_list l x n h)[i] = l[i] :=
by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp[add'_list]
    | succ n' =>
      simp[add'_list, List.getElem_set,  if_neg (by omega : ¬(n' / 2 = i))]
      apply ih (n'/2)
      { omega }
      { omega }




lemma add'_list_eq (l : List ℕ) (x:ℕ) (n : ℕ) (h : n < l.length) (i:ℕ) (hi: i >= n)
(hii : i  < l.length ) :
(add'_list l x n h)[i] = l[i] :=
by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    cases n with
    | zero => simp[add'_list]
    | succ n' =>
      simp[add'_list, List.getElem_set, if_neg (by omega : ¬(n' / 2 = i))]
      apply ih (n'/2)
      { omega }
      { omega }




def add' (st : segmentTree) (x:ℕ) (n : ℕ) (h2: n < st.l.length)  : segmentTree :=
{ l := (add'_list (st.l) x n h2).set n (x+st.l[n]'h2)
  orig_size := st.orig_size }

macro_rules
| `(tactic| get_elem_tactic_trivial) =>
 `(tactic| simp[add', len_add'_list, proper_i_lt_orig_size_minus_one_lt_len,
    proper_2i_1_lt_orig_size_minus_one_lt_len, proper_2i_2_lt_orig_size_minus_one_lt_len];
     rw[proper_len_eq_2orig_size_minus_one] at *; omega; all_goals assumption)





theorem add_correctness' (st :segmentTree) (x:ℕ) (n : ℕ) (h : n < st.l.length) (hv: proper st)
: ∀ (i : ℕ) (hh : i < st.orig_size - 1),
  (add' st x n h).l[i] = (if (i = n) then x else 0) +
  (add' st x n h).l[2 * i + 1] + (add' st x n h).l[2 * i + 2] :=
by
  intro i hi
  simp [add']
  cases hv with
  | intro hh1 hh2 hh3 =>
    induction n using Nat.strong_induction_on with
    | h v ih =>
      cases v with
      | zero =>
        simp[add'_list, List.getElem_set]
        cases Classical.em (0 = i) with
        | inl hi_zero =>
          simp[if_pos hi_zero, if_pos (symm hi_zero),
        hi_zero, hh3 i hi]
          ac_rfl
        | inr hi_zero =>
          simp[if_neg hi_zero, if_neg (by omega : ¬(i = 0)),
        hi_zero, hh3 i hi]
      | succ n' =>
        cases Classical.em (n' + 1 = i) with
        | inl hni =>
          simp[List.getElem_set, if_pos hni, if_neg (by omega : ¬(n' = 2*i)),
          if_neg (by omega : ¬(n' = 2*i+1)),  if_pos (symm hni),
          add'_list_eq st.l x (n'+1) h (2*i+1) (by omega) (by omega),
          add'_list_eq st.l x (n'+1) h (2*i+2) (by omega) (by omega)]
          simp[hni, hh3 i hi]
          ac_rfl
        | inr hni =>
          cases Classical.em (n' + 1 = 2*i+1) with
          | inl hni2 =>
            simp[List.getElem_set,if_neg hni, if_pos (by omega: n' = 2*i),
            if_neg (by omega : ¬(n' = 2 * i + 1)), add'_list, if_pos (by omega : n'/2 = i),
            if_neg (by omega : ¬(i = n'+1)), if_neg (by omega: ¬(n' / 2 = 2 * i + 2)),
             add'_list_eq st.l x (n'/2) (by omega) (2*i+2) (by omega) (by omega)]
            simp[hni2, (by omega : n'/2 = i), hh3 i hi]
            ac_rfl
          | inr hni2 =>
            cases Classical.em (n' + 1 = 2*i+2) with
            | inl hni3 =>
              simp [List.getElem_set,if_neg hni, if_neg (by omega: ¬(n' = 2*i)),
               if_neg (by omega : ¬(i = n'+1)), if_pos (by omega : n' = 2*i+1),
               add'_list, if_pos (by omega : n'/2 = i), if_neg (by omega: ¬(n' / 2 = 2 * i + 1)),
               add'_list_eq st.l x (n'/2) (by omega) (2*i+1) (by omega) (by omega)]
              simp[hni3, (by omega : n'/2 = i), hh3 i hi]
              ac_rfl
            | inr hni3 =>
              simp[List.getElem_set, if_neg hni, if_neg (by omega : ¬(i = n'+1)),
              if_neg (by omega: ¬(n' = 2*i)), if_neg (by omega : ¬(n' = 2 * i + 1))]
              simp[add'_list, ih (n'/2) (by omega)]
              intro contra
              have not_i_eq_n_half : ¬(i = n'/2) :=by omega
              simp [contra] at not_i_eq_n_half





def add (st :segmentTree) (x:ℕ) (n : ℕ) (h : n < st.orig_size) (hv: proper st) : segmentTree :=
add' st x (st.l.length/2 + n) (proper_n_plus_half_len_lt_len st n h hv)


theorem add_correctness_proper (st :segmentTree) (x:ℕ) (n : ℕ) (h : n < st.orig_size) (hv: proper st) : proper (add st x n h hv) :=
by
  apply proper.intro
  { intro i hi
    simp[add, add'] at hi
    simp[add]

    have not_if : ¬(i = (st.l.length / 2 + n)) :=
    by
      have contra : st.l.length / 2 + n >= st.orig_size - 1 :=  proper_n_plus_half_len_gt_orig_size st n hv
      omega

    have if_eq_zero (y:ℕ): 0+y=(if i = (st.l.length / 2 + n) then x else 0)+y  :=
    by
      simp[not_if]

    apply (by simp : (∀ (a b c :ℕ), (a = 0+b+c) → a=b+c))
    nth_rewrite 1 [if_eq_zero]
    apply add_correctness'
    apply hv
    apply hi }
  { cases hv with
    | intro h1 h2 h3 => simp[add,add', h1] }
  { simp [add, add', List.length_set, len_add'_list]
    cases hv with
    | intro h1 h2 h3 => apply h2 }



#check proper_orig_size_index_lt_len



theorem add_correctness_my_get_i (st :segmentTree) (x:ℕ) (n : ℕ) (h : n < st.orig_size) (hv: proper st) :
forall i, (h1:i < st.orig_size) → ¬(i = n) →
my_get (add st x n h hv) i (by simp[add, add', len_add'_list]; apply proper_orig_size_index_lt_len st hv i h1)
= my_get st i (proper_orig_size_index_lt_len st hv i h1) :=
by
  intro i hi1 hi2
  simp[add, add', my_get, List.getElem_set]
  have n_len_orig_size : ¬(st.l.length / 2 +n = i+ st.orig_size-1 ) :=
  by
    simp[proper_orig_size_eq_half_len st hv]
    omega
  simp[n_len_orig_size]
  rw[ add'_list_eq_strong]
  have middle : (st.l.length / 2 + n - 1) / 2 < st.orig_size - 1 :=
  by
    rw[proper_orig_size_eq_half_len st hv]
    omega
  omega

theorem add_correctness_my_get_n (st :segmentTree) (x:ℕ) (n : ℕ) (h : n < st.orig_size) (hv: proper st) :
my_get (add st x n h hv) n (by simp[add, add', len_add'_list]; apply proper_orig_size_index_lt_len st hv n h)
= my_get st n (proper_orig_size_index_lt_len st hv n h) + x:=
by
  simp[add, add', my_get, List.getElem_set]
  have eq: st.l.length / 2 + n = n + st.orig_size - 1 := by simp[proper_orig_size_eq_half_len st hv]; omega
  simp[eq, add_comm]

#check List.get




lemma sum_simple (st :segmentTree) (hv: proper st) (a b : ℕ) (hab: a ≤ b)
 (hb: 2*b < st.l.length ) : sum st.l a b hab (by omega) = sum st.l (2*a+1) (2*b+1) (by linarith) (by omega):=
  if heq: a=b then
    show sum st.l a b hab (by omega) =  sum st.l (2*a+1) (2*b+1) (by linarith) (by omega) from
    by
      simp[heq, sum]
  else
    show _ from
    by
      rw[sum_cut_one_left st.l a b (by omega : a < b) (by omega)]
      apply symm
      rw[sum_cut_two_left st a b (by omega : a < b) hb]
      simp[(sum_simple st hv (a+1) b (by omega) hb :  sum st.l (a+1) b (by omega) (by omega) = sum st.l (2*a+3) (2*b+1) (by omega) (by omega)), (by omega : ∀ a, 2*(a+1)+1 = 2*a+3)]
      cases hv with
      | intro hh1 hh2 hh3 =>
        simp[(hh3 a (by omega))]


def query (st : segmentTree) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.l.length): ℕ :=
 if h1 : a = b then 0 else
(if a % 2 = 0 then st.l[a] else 0) + (if ¬((b-1) % 2 = 0) then st.l[b-1] else 0)+
query st (a/2) ((b-1)/2) (by omega) (by omega)
 termination_by (b-a)




theorem query_correctness  (st : segmentTree) (hv : proper st) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.l.length):
query st a b h hb = sum st.l a b h hb :=
 if heq : a = b then
  show _ from
  by
    simp[heq, sum, query]
 else
  show _ from
  by
    cases (Nat.even_or_odd' a) with
    | intro n horn =>
      cases horn with
      | inl heva =>
        cases (Nat.even_or_odd' b) with
        | intro m horm =>
          cases horm with
          | inl hevb =>
            rw[query]
            simp [heq]
            simp[heva, hevb, (by omega : (2 * m - 1) % 2 = 1),
            sum_cut_one_right st.l (2*n) (2*m) (by omega) (by omega),
            sum_cut_one_left st.l (2*n) (2*m-1) (by omega) (by omega),
             sum_simple st hv n ((2 * m - 1) / 2) (by omega) (by omega),
             (by omega : 2 * ((2 * m - 1) / 2) + 1 = 2*m-1), query_correctness st hv n ((2*m-1)/2) (by omega) (by omega)]
            ac_rfl
          | inr hoddb =>
            rw[query]
            simp [heq]
            simp[heva, hoddb, sum_cut_one_left st.l (2*n) (2*m+1) (by omega) (by omega),
              sum_simple st hv n m (by omega) (by omega), query_correctness st hv n m (by omega) (by omega)]
      | inr hodda =>
        cases (Nat.even_or_odd' b) with
        | intro m horm =>
          cases horm with
          | inl hevb =>
            rw[query]
            simp [heq]
            simp[hodda, (by omega : (2 * n + 1) % 2 = 1), hevb, (by omega : (2 * m - 1) % 2 = 1),
              sum_cut_one_right st.l (2*n+1) (2*m) (by omega) (by omega),
               (by omega : (2 * m - 1) / 2 = m-1), (by omega : (2 * n + 1) / 2 = n),
               sum_simple st hv n (m-1) (by omega) (by omega), (by omega : (2 * (m-1) + 1) = 2*m-1),query_correctness st hv n (m-1) (by omega) (by omega)]
            ac_rfl
          | inr hoddb =>
            rw[query]
            simp [heq]
            simp[hodda, hoddb,(by omega : (2 * n + 1) % 2 = 1), (by omega : (2 * n + 1)/2 = n),
              sum_simple st hv n m (by omega) (by omega), query_correctness st hv n m (by omega) (by omega)]
termination_by (b-a)



def my_query (st : segmentTree) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b + st.orig_size -1 ≤ st.l.length)
:=  query st (a+st.orig_size-1) (b+st.orig_size-1) (by omega) (by omega)

theorem query_correctness_my_sum (st : segmentTree) (hv : proper st) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.orig_size):
my_query st a b h (by simp[proper_len_eq_2orig_size_minus_one st hv]; omega) =
my_sum st a b h (by simp[proper_len_eq_2orig_size_minus_one st hv]; omega) (by cases hv; omega) :=
by
    rw[←my_sum_sum st a b h (by cases hv; omega) (by cases hv; omega)]
    rw[my_query]
    apply query_correctness
    apply hv
