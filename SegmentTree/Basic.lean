import SegmentTree



/- We store a segment tree as an array (a list) of
2*n−1 elements where n is the size of the original array.
Each internal tree node with index i< n−1 contains sum of child nodes
2*i+1 and 2*i+2.
The elements of the original array are in indices ranging from n-1 to 2*n-2.
-/

structure segmentTree (α : Type) [AddCommMonoid α]  where
  l : List α
  orig_size : ℕ
  h1 : orig_size > 0
  h2 : l.length = 2 * orig_size - 1
  h3 :  ∀i, (hh : i < orig_size - 1) -> l[i] =  l[2*i+1] + l[2*i+2]



/- Some auxiliary lemmas
  on the relationship between
  length and indices within a segmentTree and the original array
-/


lemma proper_len_eq_2orig_size_minus_one {α : Type} [AddCommMonoid α] (st : segmentTree α )  : st.l.length  = 2*st.orig_size-1 :=
by
  simp[st.h2]

lemma proper_orig_size_eq_half_len  {α : Type} [AddCommMonoid α] (st : segmentTree α )  : st.l.length / 2 = st.orig_size-1 :=
by
  simp[st.h2]
  omega

lemma proper_orig_size_index_lt_len  {α : Type} [AddCommMonoid α] (st : segmentTree α )  :
∀ i, i < st.orig_size -> i + st.orig_size - 1 < st.l.length :=
by
  intro i hi
  simp[st.h2]
  omega

lemma proper_n_plus_half_len_lt_len  {α : Type} [AddCommMonoid α] (st : segmentTree α )  (n :ℕ) (h : n < st.orig_size) : st.l.length / 2 + n < st.l.length :=
by
  simp[st.h2]
  omega

lemma  proper_n_plus_half_len_gt_orig_size  {α : Type} [AddCommMonoid α] (st : segmentTree α )  (n:ℕ)  :  st.l.length / 2 + n >= st.orig_size - 1 :=
by
  simp[st.h2]
  omega

lemma proper_i_lt_orig_size_minus_one_lt_len  {α : Type} [AddCommMonoid α] (st : segmentTree α )  :
∀ i, i < st.orig_size - 1 -> i < st.l.length :=
by
  simp[st.h2]
  omega


lemma proper_2i_1_lt_orig_size_minus_one_lt_len  {α : Type} [AddCommMonoid α] (st : segmentTree α )  :
∀ i, i < st.orig_size - 1 -> 2*i+1 < st.l.length :=
by
  intro i hi
  simp[st.h2]
  omega

lemma proper_2i_2_lt_orig_size_minus_one_lt_len {α : Type} [AddCommMonoid α] (st : segmentTree α )   :
∀ i, i < st.orig_size - 1 -> 2*i + 2 < st.l.length :=
by
  intro i hi
  simp[st.h2]
  omega

macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simp[proper_n_plus_half_len_lt_len])



/- Definition of the sum function for a regular list -/

def sum {α : Type} [AddCommMonoid α]
(l: List α) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= l.length): α :=
 if h1 : a = b then 0 else
 have h2 : a+1 ≤ b := by omega
 l[a] + sum l (a+1) b h2 hb
 termination_by (b-a)


macro_rules | `(sum! $l $a $b) => `(sum $l $a $b (by omega) (by omega))


/-Useful lemmas that allow you to "pinch off"
  elements separately from the sum, when needed, from the right and from the left-/
lemma sum_cut_one_left {α : Type} [AddCommMonoid α]
(l: List α) (a b : ℕ) (hab: a < b) (h : b ≤ l.length) :
sum! l a b = l[a] + sum! l (a+1) b :=
 by
  have m : ¬(a=b) := by omega
  rw[sum]
  simp[m]



lemma sum_cut_one_right {α : Type} [AddCommMonoid α]
(l: List α) (a : ℕ) (b : ℕ) (h: a<b) (hb : b <= l.length):
sum! l a b = sum! l a (b-1) + l[b-1] :=
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


lemma sum_cut_two_left {α : Type} [AddCommMonoid α]  (st :segmentTree α)  (a b : ℕ) (hab: a < b)
 (hb: 2*b < st.l.length ) :
  sum! st.l (2*a+1) (2*b+1) = st.l[2*a+1] + st.l[2*a+2] + sum! st.l (2*a+3) (2*b+1) :=
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



/- Definition of the function that allows the user to retrieve
  an element stored in a segment tree by index-/


def my_get {α : Type} [AddCommMonoid α]  (st :segmentTree α)  (i : ℕ) (h: i+st.orig_size-1 < st.l.length) : α :=
 st.l[i+st.orig_size-1]

instance {α : Type} [AddCommMonoid α] : GetElem (segmentTree α) ℕ α (fun st i => i+st.orig_size-1 < st.l.length) where
  getElem st i h := my_get st i h

/- Definition of the function that allows the user to sum, at given indices,
   the elements stored in a segment tree-/

def my_sum {α : Type} [AddCommMonoid α]  (st :segmentTree α)  (a : ℕ) (b : ℕ) (h: a≤b) (hb: b+st.orig_size-1 ≤ st.l.length)
(hl : st.orig_size > 0) : α :=
 if h1 : a = b then 0 else
 st[a] + my_sum st (a+1) b (by omega) hb hl
 termination_by (b-a)

macro_rules | `(my_sum! $st $a $b) => `(my_sum $st $a $b (by omega) (by first | simp[proper_len_eq_2orig_size_minus_one]; omega | omega) (by first | apply segmentTree.h1 | omega))

/-Lemma on the relationship of two functions
 (summation of a list in range (a+st.orig_size-1),(b+st.orig_size-1) =
 = summation of a tree in range a,b)-/
lemma my_sum_sum  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (a : ℕ) (b : ℕ) (h: a≤b)
(hb: b+st.orig_size-1 ≤ st.l.length) (hl : st.orig_size > 0):
sum! st.l (a+st.orig_size-1) (b+st.orig_size-1) = my_sum! st a b :=
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
    rfl



/- Definition of a function that initializes a tree of segments to zeros
  and its correctness-/
def init {α : Type} [AddCommMonoid α] (n : ℕ) (h : n > 0) : segmentTree α :=
 { l := List.replicate (2*n-1) 0
   orig_size := n
   h1 := h
   h2 := by simp[List.replicate]
   h3 := by simp[List.replicate]
   }



macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simp[*, init]; omega)



theorem init_correctness {α : Type} [AddCommMonoid α] (result : segmentTree α) (n : ℕ) (h : 0 < n) (h1: result = init n h) :
   ∀ i, (h2: i < n) -> result[i] = 0 :=
by
  intro i hin
  simp[getElem]
  rw[my_get]
  simp[h1, init]



/-
Helper function
that updates all elements in a list that are "above" in the tree of segments by index
-/


def add_list {α : Type} [AddCommMonoid α]
(l: List α) (x:α) (n : ℕ) (h : n < l.length) : List α :=
match n with
| 0 => l
| n+1 => (add_list l x (n/2) (by omega)).set (n/2) (x+l[n/2])



lemma len_add_list {α : Type} [AddCommMonoid α]
(l: List α) (x:α) (n : ℕ) (h : n < l.length) :
(add_list l x n h).length = l.length :=
by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp[add_list]
    | succ n' =>
      simp [add_list]
      apply ih
      apply Nat.div_lt_of_lt_mul
      linarith

macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simp[len_add_list]; assumption)



/-
  Two lemmas about the nature of the changes of this operation:
  this operation leaves the element itself untouched,
  only those that stand above it in the tree of segments
-/
lemma add_list_eq_strong {α : Type} [AddCommMonoid α]
(l: List α) (x:α) (n : ℕ) (h : n < l.length) (i:ℕ) (hi: i > (n-1)/2)
(hii : i  < l.length ) :
(add_list l x n h)[i] = l[i] :=
by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp[add_list]
    | succ n' =>
      simp[add_list, List.getElem_set,  if_neg (by omega : ¬(n' / 2 = i))]
      apply ih (n'/2)
      { omega }
      { omega }




lemma add_list_eq {α : Type} [AddCommMonoid α]
(l: List α) (x:α) (n : ℕ) (h : n < l.length) (i:ℕ) (hi: i >= n)
(hii : i  < l.length ) :
(add_list l x n h)[i] = l[i] :=
by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp[add_list]
    | succ n' =>
      simp[add_list, List.getElem_set, if_neg (by omega : ¬(n' / 2 = i))]
      apply ih (n'/2)
      { omega }
      { omega }



/-
Helper function before defining the add operation -
updates all elements of the segment tree, returns a list.
Requires an internal index for the segment tree, so the operation is not available to the user
-/

def add_aux  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (x:α) (n : ℕ) (h2: n < st.l.length)  : List α :=
(add_list (st.l) x n h2).set n (x+st.l[n]'h2)


macro_rules
| `(tactic| get_elem_tactic_trivial) =>
 `(tactic| simp[add_aux, len_add_list, proper_i_lt_orig_size_minus_one_lt_len,
    proper_2i_1_lt_orig_size_minus_one_lt_len, proper_2i_2_lt_orig_size_minus_one_lt_len];rw[proper_len_eq_2orig_size_minus_one] at *; omega; all_goals assumption )

/-
An important property of this operation is the following equality:
-/


theorem add_aux_property  {α : Type} [AddCommMonoid α]  (st :segmentTree α)
 (x:α) (n : ℕ) (h : n < st.l.length)
: ∀ (i : ℕ) (hh : i < st.orig_size - 1),
  (add_aux st x n h)[i] = (if (i = n) then x else 0) +
  (add_aux st x n h)[2 * i + 1] + (add_aux st x n h)[2 * i + 2] :=
by
  intro i hi
  simp [add_aux]
  induction n using Nat.strong_induction_on with
  | h v ih =>
    have hh1 : st.orig_size > 0 := st.h1
    have hh2 : st.l.length = 2 * st.orig_size - 1 := st.h2
    have hh3 : ∀ (i : ℕ) (hh : i < st.orig_size - 1), st.l[i] = st.l[2 * i + 1] + st.l[2 * i + 2] := st.h3
    cases v with
    | zero =>
      simp[add_list, List.getElem_set]
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
        add_list_eq st.l x (n'+1) h (2*i+1) (by omega) (by omega),
        add_list_eq st.l x (n'+1) h (2*i+2) (by omega) (by omega)]
        simp[hni, hh3 i hi]
        ac_rfl
      | inr hni =>
        cases Classical.em (n' + 1 = 2*i+1) with
        | inl hni2 =>
          simp[List.getElem_set,if_neg hni, if_pos (by omega: n' = 2*i),
          if_neg (by omega : ¬(n' = 2 * i + 1)), add_list, if_pos (by omega : n'/2 = i),
          if_neg (by omega : ¬(i = n'+1)), if_neg (by omega: ¬(n' / 2 = 2 * i + 2)),
            add_list_eq st.l x (n'/2) (by omega) (2*i+2) (by omega) (by omega)]
          simp[hni2, (by omega : n'/2 = i), hh3 i hi]
          ac_rfl
        | inr hni2 =>
          cases Classical.em (n' + 1 = 2*i+2) with
          | inl hni3 =>
            simp [List.getElem_set,if_neg hni, if_neg (by omega: ¬(n' = 2*i)),
              if_neg (by omega : ¬(i = n'+1)), if_pos (by omega : n' = 2*i+1),
              add_list, if_pos (by omega : n'/2 = i), if_neg (by omega: ¬(n' / 2 = 2 * i + 1)),
              add_list_eq st.l x (n'/2) (by omega) (2*i+1) (by omega) (by omega)]
            simp[hni3, (by omega : n'/2 = i), hh3 i hi]
            ac_rfl
          | inr hni3 =>
            simp[List.getElem_set, if_neg hni, if_neg (by omega : ¬(i = n'+1)),
            if_neg (by omega: ¬(n' = 2*i)), if_neg (by omega : ¬(n' = 2 * i + 1))]
            simp[add_list]
            rw[ih (n'/2) (by omega),  if_neg (by omega: ¬(i = n'/2))]
            rw[zero_add]




/-
  A function that allows the user to add something to a specific element with a given index
-/

def add {α : Type} [AddCommMonoid α]  (st :segmentTree α) (x:α) (n : ℕ) (h : n < st.orig_size)  : segmentTree α :=
{ l := add_aux st x (st.l.length/2 + n) (proper_n_plus_half_len_lt_len st n h)
  orig_size := st.orig_size
  h1 := by simp[st.h1]
  h2 := by simp [add_aux, List.length_set, len_add_list, st.h2]
  h3 :=
  by
    intro i hi

    have not_if : ¬(i = (st.l.length / 2 + n)) :=
    by
      have contra : st.l.length / 2 + n >= st.orig_size - 1 :=  proper_n_plus_half_len_gt_orig_size st n
      omega

    have if_eq_zero (y:α): 0+y=(if i = (st.l.length / 2 + n) then x else 0)+y  :=
    by
      simp[not_if]

    apply (by simp : (∀ (a b c :α), (a = 0+b+c) → a=b+c))
    nth_rewrite 1 [if_eq_zero]
    apply add_aux_property
    apply hi

}




#check proper_orig_size_index_lt_len


macro_rules
| `(tactic| get_elem_tactic_trivial) =>
 `(tactic| apply proper_orig_size_index_lt_len; omega )
macro_rules
| `(tactic| get_elem_tactic_trivial) =>
 `(tactic| simp[add, add_aux, len_add_list]; apply proper_orig_size_index_lt_len; omega )



/- All elements
   in the segment tree except the given one remain unchanged after this operation-/
theorem add_correctness_my_get_i  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (x:α) (n : ℕ) (h : n < st.orig_size)  :
forall i, (h1:i < st.orig_size) → ¬(i = n) →
(add st x n h)[i] = st[i] :=
by
  intro i hi1 hi2
  simp[getElem]
  simp[add, add_aux, my_get, List.getElem_set]
  have n_len_orig_size : ¬(st.l.length / 2 +n = i+ st.orig_size-1 ) :=
  by
    simp[proper_orig_size_eq_half_len st]
    omega
  simp[n_len_orig_size]
  rw[ add_list_eq_strong]
  have middle : (st.l.length / 2 + n - 1) / 2 < st.orig_size - 1 :=
  by
    rw[proper_orig_size_eq_half_len st]
    omega
  omega

theorem add_correctness_my_get_n  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (x:α) (n : ℕ) (h : n < st.orig_size) :
(add st x n h)[n] = st[n] + x:=
by
  simp[getElem]
  simp[add, add_aux, my_get, List.getElem_set]
  have eq: st.l.length / 2 + n = n + st.orig_size - 1 := by simp[proper_orig_size_eq_half_len st]; omega
  simp[eq, add_comm]


#check List.get



/-
An important lemma that uses the "sum" property of the segment tree
-/

lemma sum_simple  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (a b : ℕ) (hab: a ≤ b)
 (hb: 2*b < st.l.length ) :
 sum! st.l a b= sum! st.l (2*a+1) (2*b+1):=
  if heq: a=b then
    show sum! st.l a b = sum! st.l (2*a+1) (2*b+1) from
    by
      simp[heq, sum]
  else
    show _ from
    by
      rw[sum_cut_one_left st.l a b (by omega : a < b) (by omega)]
      apply symm
      rw[sum_cut_two_left st a b (by omega : a < b) hb]
      simp[(sum_simple st (a+1) b (by omega) hb : sum! st.l (a+1) b = sum! st.l (2*a+3) (2*b+1)), (by omega : ∀ a, 2*(a+1)+1 = 2*a+3)]
      rw[←st.h3]
      simp[st.h2] at *
      omega



/-
The "helper" query function : query is to find the sum of elements in a certain
subsegment of the array, so the query function requires two numbers, the left and right border

This function is not available to the user
because it allows summing even outside the range of indices of the original elements.
-/

def query  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.l.length): α :=
 if h1 : a = b then 0 else
(if a % 2 = 0 then st.l[a] else 0) + (if ¬((b-1) % 2 = 0) then st.l[b-1] else 0)+
query st (a/2) ((b-1)/2) (by omega) (by omega)
 termination_by (b-a)

macro_rules | `(query! $st $a $b) => `(query $st $a $b (by omega) (by omega))



theorem query_correctness  {α : Type} [AddCommMonoid α]  (st :segmentTree α) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.l.length):
query! st a b  = sum! st.l a b:=
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
             sum_simple st n ((2 * m - 1) / 2) (by omega) (by omega),
             (by omega : 2 * ((2 * m - 1) / 2) + 1 = 2*m-1), query_correctness st n ((2*m-1)/2) (by omega) (by omega)]
            ac_rfl
          | inr hoddb =>
            rw[query]
            simp [heq]
            simp[heva, hoddb, sum_cut_one_left st.l (2*n) (2*m+1) (by omega) (by omega),
              sum_simple st n m (by omega) (by omega), query_correctness st n m (by omega) (by omega)]
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
               sum_simple st n (m-1) (by omega) (by omega), (by omega : (2 * (m-1) + 1) = 2*m-1),query_correctness st n (m-1) (by omega) (by omega)]
            ac_rfl
          | inr hoddb =>
            rw[query]
            simp [heq]
            simp[hodda, hoddb,(by omega : (2 * n + 1) % 2 = 1), (by omega : (2 * n + 1)/2 = n),
              sum_simple st n m (by omega) (by omega), query_correctness st n m (by omega) (by omega)]
termination_by (b-a)



/-
The query function : query is to find the sum of elements in a certain
subsegment of the array, so the query function requires two numbers, the left and right border

This function is available to the user
because it allows summing only inside the range of indices of the original elements.
-/

def my_query {α : Type} [AddCommMonoid α]  (st :segmentTree α) (a : ℕ) (b : ℕ) (h: a≤b) (hb : b + st.orig_size -1 ≤ st.l.length)
:=  query! st (a+st.orig_size-1) (b+st.orig_size-1)

macro_rules | `(my_query! $st $a $b) => `(my_query $st $a $b (by omega) (by simp[proper_len_eq_2orig_size_minus_one]; omega))

theorem my_query_correctness_my_sum  {α : Type} [AddCommMonoid α]  (st :segmentTree α)  (a : ℕ) (b : ℕ) (h: a≤b) (hb : b <= st.orig_size):
my_query! st a b = my_sum! st a b :=
by
    rw[←my_sum_sum st a b h (by simp[st.h2]; omega) st.h1]
    rw[my_query]
    apply query_correctness
    omega
    simp[st.h2]
    omega
