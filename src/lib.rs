#![feature(box_patterns)]
#![feature(box_syntax)]

use std::convert::From;
use std::ops::{Mul, Add, Div, Sub, Neg, BitXor};

#[derive(Clone, Debug, PartialEq)]
pub enum Func {
    Add(Box<Func>, Box<Func>),
    Const(f64),
    Constrainted(Box<Func>, Constraint),
    Ln(Box<Func>),
    Mul(Box<Func>, Box<Func>),
    Neg(Box<Func>),
    Pow(Box<Func>, Box<Func>),
    Rec(Box<Func>),
    Var(u32),
    X,
}

impl Mul for Func {
    type Output = Func;
    fn mul(self, rhs: Func) -> Func {
        Func::Mul(box self, box rhs)
    }
}
impl Add for Func {
    type Output = Func;
    fn add(self, rhs: Func) -> Func {
        Func::Add(box self, box rhs)
    }
}
impl Div for Func {
    type Output = Func;
    fn div(self, rhs: Func) -> Func {
        Func::Mul(box self, box Func::Rec(box rhs))
    }
}
impl Sub for Func {
    type Output = Func;
    fn sub(self, rhs: Func) -> Func {
        Func::Add(box self, box Func::Neg(box rhs))
    }
}
impl Neg for Func {
    type Output = Func;
    fn neg(self) -> Func {
        Func::Neg(box self)
    }
}
// WARNING! Terrible abuse of `^`.
impl BitXor for Func {
    type Output = Func;
    fn bitxor(self, rhs: Func) -> Func {
        Func::Pow(box self, box rhs)
    }
}

impl From<f64> for Func {
    fn from(n: f64) -> Func {
        Func::Const(n)
    }
}

#[derive(Clone, Debug, Copy, PartialEq)]
pub enum Constraint {
    Positive,
    NonZero,
    NonOne,
}

impl Func {
    pub fn derivative(self) -> Func {
        use Func::*;
        use Constraint::*;

        match self {
            Add(f, g) => f.derivative() + g.derivative(),
            Const(n) => Const(n),
            Constrainted(f, con) => f.derivative().rule(con),
            Ln(f) => f.clone().derivative() / f.rule(Positive).rule(NonOne),
            Mul(box f, box g) => f.clone().derivative() * g.clone() + f * g.derivative(),
            Neg(f) => -f.derivative(),
            Pow(box f, box g) => (f.clone() ^ g.clone()) * (f.clone().derivative() * g.clone() / f.clone() + g.derivative() * f.ln()),
            Rec(box f) => -f.clone().derivative().rule(NonZero) / f.clone() / f,
            Var(_) => Const(0.0),
            X => Const(1.0),
        }
    }

    fn _simplify(self) -> Func {
        use Func::*;

        match {self} { // hackiest hack of all hacks, see #16223.
            /* TODO remove
            // We want to place constants on left-hand side.
            Add(f, Const(n)) => (n.into() + f.simplify()).simplify(),
            Mul(f, Const(n)) => (n.into() * f.simplify()).simplify(),
            // Multiplication on the left.
            Add(f, Mul(g, h)) => g.simplify() * h.simplify() + f.simplify(),
            Mul(f, Mul(g, h)) => g.simplify() * h.simplify() * f.simplify(),
            // Addition on the left.
            Mul(f, Add(g, h)) => (g.simplify() + h.simplify()) * f.simplify(),
            Add(f, Add(g, h)) => g.simplify() + h.simplify() + f.simplify(),
            */
            // Constant folding.
            Add(box Const(a), box Const(b)) => Const(a + b),
            Mul(box Const(a), box Const(b)) => Const(a * b),
            // Constant evaluation.
            Neg(box Const(a)) => Const(-a),
            Rec(box Const(a)) => Const(1.0 / a),
            // Identity.
            Add(box Const(0.0), x) => x.simplify(),
            Mul(box Const(1.0), x) => x.simplify(),
            Neg(box Neg(x)) => x.simplify(),
            Rec(box Rec(x)) => x.simplify(),
            // Distributive property.
            Mul(f, box Add(g, h)) => {
                let dist = f.simplify();
                dist.clone() * g.simplify() + dist * h.simplify()
            },
            Pow(box Mul(f, g), h) => {
                let dist = h.simplify();
                (f.simplify() ^ dist.clone()) * (g.simplify() ^ dist)
            }
            Neg(box Add(f, g)) => -f.simplify() + -g.simplify(),
            Rec(box Mul(f, g)) => f.rec() * g.rec(),
            // Power laws.
            Pow(box Pow(f, g), h) => f.simplify() ^ (g.simplify() * h.simplify()),
            // Logarithms.
            Ln(box Mul(f, g)) => f.simplify().ln() + g.simplify().ln(),
            // Associativity.
            Add(box Add(f, g), h) => f.simplify() + (g.simplify() + h.simplify()),
            Mul(box Mul(f, g), h) => f.simplify() * (g.simplify() * h.simplify()),
            // Commutativity + catch the subexpressions.
            Add(f, g) => {
                if let box Neg(ref x) = g {
                    if *x == f {
                        return 0.0.into();
                    }
                }

                if f == g {
                    Const(2.0) * g.simplify()
                } else {
                    f.simplify() + g.simplify()
                }
            },
            Mul(f, g) => {
                if let box Rec(ref x) = g {
                    if *x == f {
                        return 1.0.into();
                    }
                }

                if f == g {
                    g.simplify() ^ Const(2.0)
                } else {
                    f.simplify() * g.simplify()
                }
            },
            // We want to walk down the tree.
            Pow(f, g) => f.simplify() ^ g.simplify(),
            Neg(f) => -f.simplify(),
            Constrainted(f, con) => f.simplify().rule(con),
            // Aw, we couldn't simplify that one.
            x => x,
        }
    }

    pub fn simplify(self) -> Func {
        let mut simp = self._simplify();
        let mut simp_old = simp.clone();
        loop {
            if simp == simp_old {
                return simp;
            }

            simp_old = simp.clone();
            simp = simp._simplify();
        }
    }

    fn ln(self) -> Func {
        Func::Ln(box self)
    }

    fn rec(self) -> Func {
        Func::Rec(box self)
    }

    fn rule(self, c: Constraint) -> Func {
        Func::Constrainted(box self, c)
    }

    pub fn to_string(&self) -> String {
        use Func::*;

        match self {
            &Add(ref a, ref b) => format!("{{ ({} + {}) }}", a.to_string(), b.to_string()),
            &Const(n) => n.to_string(),
            &Constrainted(ref a, _) => a.to_string(),
            &Ln(ref a) => format!("\\ln{{ {} }}", a.to_string()),
            &Mul(ref a, ref b) => format!("{} {}", a.to_string(), b.to_string()),
            &Neg(ref a) => format!("(-{})", a.to_string()),
            &Pow(ref a, ref b) => format!("{} ^ {{ {} }}", a.to_string(), b.to_string()),
            &Rec(ref a) => format!("\\frac{{1}}{{ {} }}", a.to_string()),
            &Var(_) => "_".to_owned(),
            &X => "x".to_owned(),
        }
    }
}

#[test]
fn test_derivative() {
    use Func::*;
    let f = (X ^ (Const(4.0))) * (X + Const(1.0));//-Const(3.0) * (X ^ Const(4.0)).ln();

    assert_eq!(&f.clone().derivative().to_string(), ""); // (X ^ X) * (Const(1.0) + X.ln()) * Const(3.0))
    assert_eq!(&f.derivative().simplify().to_string(), "a"); // (X ^ X) * (Const(1.0) + X.ln()) * Const(3.0))
}
