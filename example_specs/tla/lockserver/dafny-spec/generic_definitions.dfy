module Generic_Defs {

predicate seqIsUnique<T>(a:seq<T>) {
    forall i, j | 0<=i<|a| && 0<=j<|a| && a[i]==a[j] :: i == j
}

lemma lemma_NonEmptySeqContainsSomeElement<T>(a:seq<T>)
    requires |a| > 0
    ensures exists e :: e in a
{
    var e := a[0];
    assert e in a;
}
}