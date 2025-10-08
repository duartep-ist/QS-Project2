
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

// lemma sumAltAddsLikeSum(a: array<int>, i: nat, j: nat)
//   requires 0 <= i < j <= a.Length
//   ensures sumAlt(a, i, j) == a[i] + sumAlt(a, i + 1, j)
// {
//   if(j == i + 1) {
//     assert sumAlt(a, i, i + 1) == a[i] + sumAlt(a, i + 1,  i + 1);
//     assert sumAlt(a, i + 1,  i + 1) == 0;
//   }
// }


// lemma aaaaa(a: array<int>, i: nat, j: nat)
//   requires 0 <= i < j < a.Length
//   ensures sum(a, i, j) == a[j-1] + sumAlt(a, i, j - 1)
// {
// }

// lemma asdkhusvd(a: array<int>, k: nat, i: nat)
//   requires 0 <= i + k <= a.Length
//   ensures sum(a, i, i + k) == sumAlt(a, i, i + k)
// {
//   if (k == 0) {
//     assert sum(a, i, i) == sumAlt(a, i, i);
//   } else {
//     assert sum(a, i, i + k - 1) == sumAlt(a, i, i + k - 1);
//     assert sum(a, , k) == a[0] + sum(a, 0 + 1, k);
//     assert sumAlt(a, 0, k) == a[k - 1] + sum(a, 0, k - 1);
//     assert sum(a, 0, k) == sumAlt(a, 0, k);
//   }
// }

// lemma sum_equiv(a: array<int>, i: nat, k: nat)
//   requires 0 <= i + k <= a.Length
//   ensures sum(a, i, i + k) == sumAlt(a, i, i + k)
// {
//   if(k == 0) {
//     assert sum(a, i, i) == sumAlt(a, i, i);
//   } else {
//     assert sum(a, i, i + k - 1) == sumAlt(a, i, i + k - 1);
//     assert sum(a, i, i + k) == a[i] + sum(a, i + 1, i + k);
//     assert sumAlt(a, i, i + k) == a[i + k - 1] + sumAlt(a, i, i + k - 1);
//   }
// }


lemma sum_equiv(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sumAlt(a, i, j)
  decreases j - i
{
  if (i == j) {

  } else {
    assert sum(a, i + 1, j) == sumAlt(a, i + 1, j);
    assert sum(a, i, j) == a[i] + sum(a, i + 1, j);
    assert sumAlt(a, i, j) == a[j - 1] + sumAlt(a, i, j - 1);
    assert sum(a, i, j - 1) == sumAlt(a, i, j - 1);
  }
}
