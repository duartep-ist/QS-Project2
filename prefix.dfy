
function sum(a: array<int>, i: nat, j: nat): int
  reads a
  requires 0 <= i <= j <= a.Length
  decreases j - i
{
  if (i == j) then 0 else a[i] + sum(a, i + 1, j)
}

function sumAlt(a: array<int>, i: nat, j: nat): int
  reads a
  requires 0 <= i <= j <= a.Length
  decreases j - i
{
  if (i == j) then 0 else a[j - 1] + sumAlt(a, i, j - 1)
}

lemma sum_equiv(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sumAlt(a, i, j)
  decreases j - i
{
  if (i == j) {
    assert sum(a, i, i) == sumAlt(a, i, i);
  } else {
    sum_equiv(a,i+1,j);
  }
}

method query(a: array<int>, i: nat, j: nat) returns (result: int)
  requires i <= j <= a.Length
  ensures result == sum(a, i, j)
{
  result := 0;
  var k := i;
  while (k < j)
    invariant i <= k <= j
    invariant result == sumAlt(a, i, k)
  {
    result := result + a[k];
    k := k + 1;
  }
  sum_equiv(a, i, j);
}
