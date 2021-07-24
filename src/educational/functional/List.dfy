type T = int

// --------------------------------------- Datatypes -------------------------------------------- //

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

// --------------------------------------- Predicates ------------------------------------------- //

predicate list_increasing(list:List<T>)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, Nil) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_increasing(Cons(ht, tail))
  }
}

predicate list_lower_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d <= head) && list_lower_bound(tail, d)
  }
}

predicate list_upper_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d >= head) && list_upper_bound(tail, d)
  }
}

// ------------------------------------ Function Methods ---------------------------------------- //

function method List_ToMultiset(list:List<T>) : (m:multiset<T>)
  decreases list
{
  match list {
    case Nil => multiset{}
    case Cons(head, tail) => multiset{head} + List_ToMultiset(tail)
  }
}

/** Properties:
 *
 *  Lemma_ListConcatIntegrity(a, b)
 *    ==> ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
 *
 *  Lemma_ListConcatBothListEmpty(List.Nil, List.Nil)
 *    ==> ensures List_Concat(a, b) == List.Nil
 *
 *  Lemma_ListConcatFirstListEmpty(List.Nil, b)
 *    ==> ensures List_Concat(List.Nil, b) == b
 *
 *  Lemma_ListConcatWithMidElemOrdering(a, x, b)
 *    ==> ensures list_increasing(List_Concat(a, Cons(x, b)))
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
    case Nil => b
    case Cons(head, tail) => Cons(head, List_Concat(tail, b))
  }
}

// ------------------------------------ List_Concat Lemmas -------------------------------------- //

lemma {:induction a} Lemma_ListConcatIntegrity(a:List<T>, b:List<T>)
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  decreases a, b
{
  match a {
    case Nil =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert a == List.Nil; }
        List_ToMultiset(List_Concat(List.Nil, b));
          { assert List_ToMultiset(List_Concat(List.Nil, b)) 
                == List_ToMultiset(List.Nil) + List_ToMultiset(b); }
        List_ToMultiset(List.Nil) + List_ToMultiset(b);
          { assert List_ToMultiset(List.Nil) == multiset{}; }
        multiset{} + List_ToMultiset(b);
          { assert multiset{} == List_ToMultiset(List.Nil); }
        List_ToMultiset(List.Nil) + List_ToMultiset(b);
          { assert List_ToMultiset(List.Nil) == List_ToMultiset(a); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert a == Cons(ha, ta); }
        List_ToMultiset(List_Concat(Cons(ha, ta), b));
          { assert List_ToMultiset(List_Concat(Cons(ha, ta), b))
                == List_ToMultiset(Cons(ha, ta)) + List_ToMultiset(b); }
        List_ToMultiset(Cons(ha, ta)) + List_ToMultiset(b);
          { Lemma_ListConcatIntegrity(ta, b); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
  }
}

lemma {:induction a, b} Lemma_ListConcatBothListEmpty(a:List<T>, b:List<T>)
  requires a == List.Nil
  requires b == List.Nil
  ensures List_Concat(a, b) == List.Nil
{
  calc == {
    List_Concat(a, b);
      { assert a == List.Nil; }
    List_Concat(List.Nil, b);
      { assert List_Concat(List.Nil, b) == b; }
    b;
      { assert b == List.Nil; }
    List.Nil;
  }
}

lemma {:induction a} Lemma_ListConcatFirstListEmpty(a:List<T>, b:List<T>)
  requires a == List.Nil
  ensures List_Concat(a, b) == b
{
  calc == {
    List_Concat(a, b);
      { assert a == List.Nil; }
    List_Concat(List.Nil, b);
      { assert List_Concat(List.Nil, b) == b; }
    b;
  }
}

lemma {:induction a, b} Lemma_ListConcatWithMidElemOrdering(a:List<T>, x:T, b:List<T>)
  requires list_increasing(a)
  requires list_increasing(b)
  requires list_lower_bound(b, x)
  requires list_upper_bound(a, x)
  ensures list_increasing(List_Concat(a, Cons(x, b)))
  decreases a, b
{
  match a {
    case Nil =>
      calc == {
        list_increasing(List_Concat(a, Cons(x, b)));
          { assert a == List.Nil; }
        list_increasing(List_Concat(List.Nil, Cons(x, b)));
          { Lemma_ListConcatFirstListEmpty(List.Nil, b); }
        list_increasing(Cons(x, b));
          { assert list_lower_bound(b, x); }
          { assert list_increasing(b); }
        true;
      }
    case Cons(ha, ta) =>
      match ta {
        case Nil =>
          calc == {
            list_increasing(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_increasing(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b)) 
                    == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_increasing(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == List.Nil; }
            list_increasing(Cons(ha, List_Concat(List.Nil, Cons(x, b))));
              { Lemma_ListConcatFirstListEmpty(List.Nil, b); }
            list_increasing(Cons(ha, Cons(x, b)));
              { assert ha <= x; }
              { assert list_lower_bound(b, x); }
              { assert list_increasing(b); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_increasing(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_increasing(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b))
                    == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_increasing(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == Cons(tah, tat); }
            list_increasing(Cons(ha, List_Concat(Cons(tah, tat), Cons(x, b))));
              { assert (ha <= tah && list_increasing(List_Concat(Cons(tah, tat), Cons(x, b)))); }
            ha <= tah && list_increasing(List_Concat(Cons(tah, tat), Cons(x, b)));
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
    case Nil =>
      calc == {
        list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List.Nil; }
        list_upper_bound(List_Concat(List.Nil, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
        list_upper_bound(Cons(x, listRight), d);
          { assert list_upper_bound(listRight, d); }
          { assert d >= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case Nil =>
          calc == {
            list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List.Nil); }
            list_upper_bound(List_Concat(Cons(lh, List.Nil), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List.Nil), Cons(x, listRight))
                    == Cons(lh, List_Concat(List.Nil, Cons(x, listRight))); }
            list_upper_bound(Cons(lh, List_Concat(List.Nil, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
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
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight))
                    == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
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
    case Nil =>
      calc == {
        list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List.Nil; }
        list_lower_bound(List_Concat(List.Nil, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
        list_lower_bound(Cons(x, listRight), d);
          { assert list_lower_bound(listRight, d); }
          { assert d <= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case Nil =>
          calc == {
            list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List.Nil); }
            list_lower_bound(List_Concat(Cons(lh, List.Nil), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List.Nil), Cons(x, listRight))
                    == Cons(lh, List_Concat(List.Nil, Cons(x, listRight))); }
            list_lower_bound(Cons(lh, List_Concat(List.Nil, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
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
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight))
                    == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
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
