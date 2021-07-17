type T = int

// -------------------------- Datatype -------------------------- //

datatype List_Empty = Nil
datatype List<T> = List_Empty | Cons(head:T, tail:List<T>)

// ---------------------- Function Methods ---------------------- //

/** Properties:
 *
 *  Lemma_ListInsertIntegrity(list, x)
 *    ==> ensures List_ToMultiset(List_Insert(list, d)) == List_ToMultiset(list) + multiset{d}
 *
 */
function method List_Insert(list:List<T>, d:T) : List<T>
  decreases list
{
  match list {
    case List_Empty => Cons(d, List_Empty)
    case Cons(head, tail) => Cons(head, List_Insert(tail, d))
  }
}


/** Properties:
 *
 *  Lemma_ListConcatIntegrity(a, b)
 *    ==> ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
 *
 *  Lemma_ListConcatSize(a, b)
 *    ==> ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
 *
 *  Lemma_ListConcatOfEmptyLists(List_Empty, List_Empty)
 *    ==> ensures List_Concat(a, b) == List_Empty
 *
 *  Lemma_ListConcatFirstListEmpty(List_Empty, b)
 *    ==> ensures List_Concat(List_Empty, b) == b
 *
 *  Lemma_ListConcatWithMidElemOrdering(a, x, b)
 *    ==> ensures list_ordered(List_Concat(a, Cons(x, b)))
 *
 *  Lemma_ListConcatUpperBound(a, b, d, x)
 *    ==> ensures list_upper_bound(List_Concat(a, Cons(x, b)), d)
 *
 *  Lemma_ListConcatLowerBound(a, b, d, x)
 *    ==> ensures list_lower_bound(List_Concat(a, Cons(x, b)), d)
 *
 */
function method List_Concat(a:List<T>, b:List<T>) : List<T>
  decreases a
{
  match a {
    case List_Empty => b
    case Cons(head, tail) => Cons(head, List_Concat(tail, b))
  }
}

function method List_ToMultiset(list:List<T>) : (m:multiset<T>)
  decreases list
{
  match list {
    case List_Empty => multiset{}
    case Cons(head, tail) => multiset{head} + List_ToMultiset(tail)
  }
}

function method List_Size(list:List<T>) : nat
  decreases list
{
  match list {
    case List_Empty => 0
    case Cons(head, tail) => 1 + List_Size(tail)
  }
}

function method List_Head(list:List<T>) : (head:T)
  requires list != List_Empty
{
  match list {
    case Cons(head, tail) => head
  }
}

function method List_Tail(list:List<T>) : (tail:List<T>)
{
  match list {
    case List_Empty => List_Empty
    case Cons(head, tail) => tail
  }
}

// ------------------------- Methods -------------------------- //

method List_Print(list:List<T>) 
  decreases list
{
  match list {
    case List_Empty => {
      return;
    }
    case Cons(head, List_Empty) => {
      print head, "\n";
      return;
    }
    case Cons(head, tail) => {
      print head, ", ";
      List_Print(tail);
    }
  }
}

// ---------------------- Predicates ---------------------- //

predicate list_ordered(list:List<T>)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, List_Empty) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_ordered(Cons(ht, tail))
  }
}

predicate list_lower_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, tail) => (d <= head) && list_lower_bound(tail, d)
  }
}

predicate list_upper_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, tail) => (d >= head) && list_upper_bound(tail, d)
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction list} Lemma_ListInsertIntegrity(list:List<T>, d:T)
  ensures List_ToMultiset(List_Insert(list, d)) == List_ToMultiset(list) + multiset{d}
  decreases list
{
  match list {
    case List_Empty =>
      calc == {
        List_ToMultiset(List_Insert(list, d));
          { assert list == List_Empty; }
        List_ToMultiset(List_Insert(List_Empty, d));
          { assert List_Insert(List_Empty, d) == Cons(d, List_Empty); }
        List_ToMultiset(Cons(d, List_Empty));
          { assert List_ToMultiset(Cons(d, List_Empty)) == List_ToMultiset(List_Empty) + multiset{d}; }
        List_ToMultiset(List_Empty) + multiset{d};
          { assert List_Empty == list; }
        List_ToMultiset(list) + multiset{d};
      }
    case Cons(head, tail) =>
      calc == {
        List_ToMultiset(List_Insert(list, d));
          { assert list == Cons(head, tail); }
        List_ToMultiset(List_Insert(Cons(head, tail), d));
          { assert List_Insert(Cons(head, tail), d) == Cons(head, List_Insert(tail, d)); }
        List_ToMultiset(Cons(head, List_Insert(tail, d)));
          { assert List_ToMultiset(Cons(head, List_Insert(tail, d))) == List_ToMultiset(List_Insert(tail, d)) + multiset{head}; }
        List_ToMultiset(List_Insert(tail, d)) + multiset{head};
          { Lemma_ListInsertIntegrity(tail, d); }
        List_ToMultiset(list) + multiset{d};
      }
  }
}

lemma {:induction a} Lemma_ListConcatIntegrity(a:List<T>, b:List<T>)
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert a == List_Empty; }
        List_ToMultiset(List_Concat(List_Empty, b));
          { assert List_ToMultiset(List_Concat(List_Empty, b)) == List_ToMultiset(List_Empty) + List_ToMultiset(b); }
        List_ToMultiset(List_Empty) + List_ToMultiset(b);
          { assert List_ToMultiset(List_Empty) == multiset{}; }
        multiset{} + List_ToMultiset(b);
          { assert multiset{} == List_ToMultiset(List_Empty); }
        List_ToMultiset(List_Empty) + List_ToMultiset(b);
          { assert List_ToMultiset(List_Empty) == List_ToMultiset(a); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(Cons(ha, List_Empty)) + List_ToMultiset(List_Concat(ta, b)); }
        List_ToMultiset(Cons(ha, List_Empty)) + List_ToMultiset(List_Concat(ta, b));
          { Lemma_ListConcatIntegrity(ta, b); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
  }
}

lemma {:induction a} Lemma_ListConcatSize(a:List<T>, b:List<T>)
  ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_Size(List_Concat(a, b));
          { assert a == List_Empty; }
        List_Size(List_Concat(List_Empty, b));
          { assert List_Size(List_Empty) == 0; }
          { assert List_Size(List_Empty) + List_Size(b) == 0 + List_Size(b); }
        0 + List_Size(b);
          { assert 0 == List_Size(List_Empty); }
        List_Size(List_Empty) + List_Size(b);
          { assert List_Size(List_Empty) == List_Size(a); }
        List_Size(a) + List_Size(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_Size(List_Concat(a, b));
          { assert List_Size(List_Concat(a, b)) == List_Size(Cons(ha, List_Empty)) + List_Size(List_Concat(ta, b)); }
        List_Size(Cons(ha, List_Empty)) + List_Size(List_Concat(ta, b));
          { Lemma_ListConcatSize(ta, b); }
        List_Size(a) + List_Size(b);
      }
  }
}

lemma {:induction a, b} Lemma_ListConcatOfEmptyLists(a:List<T>, b:List<T>)
  requires a == List_Empty
  requires b == List_Empty
  ensures List_Concat(a, b) == List_Empty
{
  calc == {
    List_Concat(a, b);
      { assert a == List_Empty; }
    List_Concat(List_Empty, b);
      { assert List_Concat(List_Empty, b) == b; }
    b;
      { assert b == List_Empty; }
    List_Empty;
  }
}

lemma {:induction a} Lemma_ListConcatFirstListEmpty(a:List<T>, b:List<T>)
  requires a == List_Empty
  ensures List_Concat(a, b) == b
{
  calc == {
    List_Concat(a, b);
      { assert a == List_Empty; }
    List_Concat(List_Empty, b);
      { assert List_Concat(List_Empty, b) == b; }
    b;
  }
}

lemma {:induction a, b} Lemma_ListConcatWithMidElemOrdering(a:List<T>, x:T, b:List<T>)
  requires list_ordered(a)
  requires list_ordered(b)
  requires list_lower_bound(b, x)
  requires list_upper_bound(a, x)
  ensures list_ordered(List_Concat(a, Cons(x, b)))
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        list_ordered(List_Concat(a, Cons(x, b)));
          { assert a == List_Empty; }
        list_ordered(List_Concat(List_Empty, Cons(x, b)));
          { Lemma_ListConcatFirstListEmpty(List_Empty, b); }
        list_ordered(Cons(x, b));
          { assert list_lower_bound(b, x); }
          { assert list_ordered(b); }
        true;
      }
    case Cons(ha, ta) =>
      match ta {
        case List_Empty =>
          calc == {
            list_ordered(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_ordered(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b)) == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_ordered(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == List_Empty; }
            list_ordered(Cons(ha, List_Concat(List_Empty, Cons(x, b))));
              { Lemma_ListConcatFirstListEmpty(List_Empty, b); }
            list_ordered(Cons(ha, Cons(x, b)));
              { assert ha <= x; }
              { assert list_lower_bound(b, x); }
              { assert list_ordered(b); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_ordered(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_ordered(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b)) == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_ordered(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == Cons(tah, tat); }
            list_ordered(Cons(ha, List_Concat(Cons(tah, tat), Cons(x, b))));
              { assert (ha <= tah && list_ordered(List_Concat(Cons(tah, tat), Cons(x, b)))); }
            ha <= tah && list_ordered(List_Concat(Cons(tah, tat), Cons(x, b)));
              { Lemma_ListConcatWithMidElemOrdering(Cons(tah, tat), x, Cons(x, b)); }
            true;
          }
      }
  }
}

lemma {:induction listLeft} Lemma_ListConcatUpperBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_upper_bound(listLeft, d)
  requires list_upper_bound(listRight, d)
  requires d >= x
  ensures list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{
  match listLeft {
    case List_Empty =>
      calc == {
        list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List_Empty; }
        list_upper_bound(List_Concat(List_Empty, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List_Empty, Cons(x, listRight)); }
        list_upper_bound(Cons(x, listRight), d);
          { assert list_upper_bound(listRight, d); }
          { assert d >= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case List_Empty =>
          calc == {
            list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List_Empty); }
            list_upper_bound(List_Concat(Cons(lh, List_Empty), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List_Empty), Cons(x, listRight)) == Cons(lh, List_Concat(List_Empty, Cons(x, listRight))); }
            list_upper_bound(Cons(lh, List_Concat(List_Empty, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List_Empty, Cons(x, listRight)); }
            list_upper_bound(Cons(lh, Cons(x, listRight)), d);
              { assert d >= x; }
              { assert list_upper_bound(listRight, d); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, lt); }
            list_upper_bound(List_Concat(Cons(lh, lt), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight)) == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
            list_upper_bound(Cons(lh, List_Concat(lt, Cons(x, listRight))), d);
              { assert lt == Cons(tah, tat); }
            list_upper_bound(Cons(lh, List_Concat(Cons(tah, tat), Cons(x, listRight))), d);
              { assert (d >= lh && list_upper_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d)); }
            d >= x && list_upper_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d);
              { Lemma_ListConcatUpperBound(Cons(tah, tat), Cons(x, listRight), d, x); }
            true;
          }
      }
  }
}

lemma {:induction listLeft} Lemma_ListConcatLowerBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_lower_bound(listLeft, d)
  requires list_lower_bound(listRight, d)
  requires d <= x
  ensures list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{
  match listLeft {
    case List_Empty =>
      calc == {
        list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List_Empty; }
        list_lower_bound(List_Concat(List_Empty, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List_Empty, Cons(x, listRight)); }
        list_lower_bound(Cons(x, listRight), d);
          { assert list_lower_bound(listRight, d); }
          { assert d <= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case List_Empty =>
          calc == {
            list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List_Empty); }
            list_lower_bound(List_Concat(Cons(lh, List_Empty), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List_Empty), Cons(x, listRight)) == Cons(lh, List_Concat(List_Empty, Cons(x, listRight))); }
            list_lower_bound(Cons(lh, List_Concat(List_Empty, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List_Empty, Cons(x, listRight)); }
            list_lower_bound(Cons(lh, Cons(x, listRight)), d);
              { assert d <= x; }
              { assert list_lower_bound(listRight, d); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, lt); }
            list_lower_bound(List_Concat(Cons(lh, lt), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight)) == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
            list_lower_bound(Cons(lh, List_Concat(lt, Cons(x, listRight))), d);
              { assert lt == Cons(tah, tat); }
            list_lower_bound(Cons(lh, List_Concat(Cons(tah, tat), Cons(x, listRight))), d);
              { assert (d <= lh && list_lower_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d)); }
            d <= lh && list_lower_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d);
              { Lemma_ListConcatLowerBound(Cons(tah, tat), Cons(x, listRight), d, x); }
            true;
          }
      }
  }
}
