ghost function exp(a: int, b: nat): int {
	if b == 0 then 1
	else a * exp(a, b-1)
}

function expAcc(a: int, b: nat, r: int): int {
	if b == 0 then r
	else expAcc(a, b-1, a*r)
}

lemma expAccEqualsExp(a: int, b: nat, r: int)
	ensures expAcc(a, b, r) == r*exp(a, b)
{
}

lemma expAccEqualsExpOne(a: int, b: nat)
	ensures expAcc(a,b,1) == exp(a,b)
{
	expAccEqualsExp(a, b, 1);
}

lemma simplifyExp(a: int, b: nat)
	ensures (
		(b % 2 == 1 && exp(a, b) == a * exp(a*a, (b-1)/2)) ||
		(b % 2 == 0 && exp(a, b) == exp(a*a, b/2))
	)
{
	if(b == 0) {
		assert exp(a, 0) == exp(a*a, 0);
	} else  {
		if(b % 2 == 0) {
			//assert exp(a, b - 1) == a*exp(a*a, (b-2)/2);
			expAccEqualsExpOne(a, b);
			assert exp(a, b) == expAcc(a,b,1);
			expAccEqualsExp(a*a, (b-2)/2, a);
			assert a*exp(a*a, (b-2)/2) == expAcc(a*a, (b-2)/2, a);
			assert exp(a, b) == expAcc(a, b - 1, a);

		} else {

		}
	}
}
