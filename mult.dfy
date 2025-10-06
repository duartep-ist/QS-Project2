lemma simplifyMult(x: int, y: int)
	ensures (
		(y % 2 == 0 && x*y == (x*2) * (y/2)) ||
		(y % 2 == 1 && x*y == x + (x*2) * ((y-1)/2))
	)
{}

method peasantMult(a: int, b: int) returns (r: int)
	requires b >= 0
	ensures r == a*b
{
	var x := a;
	var y := b;
	r := 0;
	while y > 0
		invariant y >= 0
		invariant r + x*y == a*b
	{
		simplifyMult(x, y);
		if y % 2 == 1 {
			r := r + x;
			y := y - 1;
		}
		x := x*2;
		y := y / 2;
	}
	return r;
}
