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

lemma simplifyExpEven(a: int, b: nat, r: int)
	requires b % 2 == 0
	ensures (expAcc(a, b, r) == expAcc(a*a, b/2, r))
	{
		if(b == 0) {
			assert expAcc(a, 0, r) == expAcc(a*a, 0, r);
		} else {
			assert expAcc(a, b - 2, r) == expAcc(a*a, (b - 2)/2, r);
			assert expAcc(a, b, r) == expAcc(a, b - 2, a*a*r);
			assert expAcc(a*a, b/2, r) == expAcc(a*a, (b - 2)/2, a*a*r);
		}
	}

lemma simplifyExpOdd(a: int, b: nat, r: int)
	requires b % 2 == 1
	ensures (expAcc(a, b, r) == expAcc(a*a, (b-1)/2, a*r))
	{
		if(b == 1) {
			assert expAcc(a, 1, r) == expAcc(a*a, 0, a*r);
		} else {
			assert expAcc(a, b, r) == expAcc(a, b - 1, a*r);
			simplifyExpEven(a, b - 1, a*r);
			assert expAcc(a, b - 1, a*r) == expAcc(a*a, (b - 1)/2, a*r);
		}
	}

lemma simplifyExp(a: int, b: nat, r: int)
	ensures (
		(b % 2 == 1 && expAcc(a, b, r) == expAcc(a*a, (b-1)/2, a*r)) ||
		(b % 2 == 0 && expAcc(a, b, r) == expAcc(a*a, b/2, r))
	)
	{
		if(b % 2 == 1) {
			simplifyExpOdd(a, b, r);
		} else {
			simplifyExpEven(a, b, r);
		}
	}

method FastExp(x: int, n: int) returns (r: int)
	requires n >= 0
	ensures r == exp(x,n)
{
	r := 1;
	var c := x;
	var b := n;
	while b > 0
		invariant b >= 0
		invariant expAcc(x, n, 1) == expAcc(c, b, r)
	{
		var pr := r;
		var pc := c;
		var pb := b;
		if b % 2 == 0 {
			simplifyExpEven(c, b, r);
			c := c * c;
			b := b / 2;
		} else {
			simplifyExpOdd(c, b, r);
			r := r * c;
			c := c * c;
			b := (b - 1) / 2;
		}
	}
	assert b == 0;
	expAccEqualsExp(c, b, r);
	expAccEqualsExp(x, n, 1);
}
