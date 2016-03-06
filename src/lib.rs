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
            // (f + g)' = f' + g'
            Add(f, g) => f.derivative() + g.derivative(),
            // c' = 0
            Const(n) => Const(0.0),
            Constrainted(f, con) => f.derivative().rule(con),
            // (ln f)' = f' / f
            Ln(f) => f.clone().derivative() / f.rule(Positive).rule(NonOne),
            // (fg)' = f'g + fg'
            Mul(box f, box g) => f.clone().derivative() * g.clone() + f * g.derivative(),
            // (-f)' = -f'
            Neg(f) => -f.derivative(),
            // (f^g)' = f^g (f' g / f + g' ln f)
            Pow(box f, box g) => (f.clone() ^ g.clone()) * (f.clone().derivative() * g.clone() / f.clone() + g.derivative() * f.ln()),
            // (f^-1)' = -f' / f^2
            Rec(box f) => -f.clone().derivative().rule(NonZero) / f.clone() / f,
            // c' = 0
            Var(_) => Const(0.0),
            // x' = 1
            X => Const(1.0),
        }
    }

    fn precedence(&self) -> u8 {
        use Func::*;

        match self {
            &Add(_, _) => 0,
            &Neg(_) => 1,
            &Mul(_, _) => 1,
            &Rec(_) => 2,
            &Pow(_, _) => 3,
            &Ln(_) => 4,
            &Const(_) => 5,
            &Var(_) => 6,
            &X => 7,
            &Constrainted(_, _) => 8,
        }
    }

    fn normalize(self) -> Func {
        use Func::*;

        match self {
            Add(f, g) => if f.precedence() <= g.precedence() {
                g.normalize() + f.normalize()
            } else {
                f.normalize() + g.normalize()
            },
            Mul(f, g) => if f.precedence() <= g.precedence() {
                g.normalize() * f.normalize()
            } else {
                f.normalize() * g.normalize()
            },
            // Recursively walk down the tree
            Neg(f) => -f.normalize(),
            Rec(f) => f.normalize().rec(),
            Ln(f) => f.normalize().ln(),
            Pow(f, g) => f.normalize() ^ g.normalize(),
            Constrainted(f, c) => f.normalize().rule(c),
            e => e,
        }
    }

    pub fn simplify(self) -> Func {
        use Func::*;

        match self.normalize() { // hackiest hack of all hacks, see #16223.
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
            Pow(box Pow(f, g), h) => f.simplify() ^ (g.simplify() * h.simplify()).simplify(),
            // Logarithms.
            Ln(box Mul(f, g)) => f.simplify().ln() + g.simplify().ln(),
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
            // TODO do commutation and associativity iff it reduce the complexity of the
            // expression.

            // We want to walk down the tree.
            Pow(f, g) => f.simplify() ^ g.simplify(),
            Neg(f) => -f.simplify(),
            Constrainted(f, con) => f.simplify().rule(con),
            // Aw, we couldn't simplify that one.
            x => x,
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

    pub fn to_latex(&self) -> String {
        use Func::*;

        match self {
            &Add(ref a, ref b) => "{(".to_owned() + &a.to_latex() + " + " + &b.to_latex() + ")}",
            &Const(n) => n.to_string(),
            &Constrainted(ref a, _) => a.to_latex(),
            &Ln(ref a) => "\\ln{".to_owned() + &a.to_latex() + "}",
            &Mul(ref a, ref b) => a.to_latex() + " \\cdot " + &b.to_latex(),
            &Neg(ref a) => "(-".to_owned() + &a.to_latex() + ")",
            &Pow(ref a, ref b) => a.to_latex() + "^{" + &b.to_latex() + "}",
            &Rec(ref a) => "\\frac{1}{".to_owned() + &a.to_latex() + "}",
            &Var(_) => "_".to_owned(),
            &X => "x".to_owned(),
        }
    }

    pub fn to_unicode(&self) -> String {
        use Func::*;

        match self {
            &Add(ref a, ref b) => "(".to_owned() + &a.to_unicode() + " + " + &b.to_unicode() + ")",
            &Const(n) => n.to_string(),
            &Constrainted(ref a, _) => a.to_unicode(),
            &Ln(ref a) => "ln(".to_owned() + &a.to_unicode() + ")",
            &Mul(ref a, ref b) => a.to_unicode() + " · " + &b.to_unicode(),
            &Neg(ref a) => "(-".to_owned() + &a.to_unicode() + ")",
            &Pow(ref a, ref b) => a.to_unicode() + "^(" + &b.to_unicode() + ")",
            &Rec(ref a) => "(".to_owned() + &a.to_unicode() + ")¯¹",
            &Var(_) => "_".to_owned(),
            &X => "x".to_owned(),
        }
    }
}

#[test]
fn test_derivative() {
    use Func::*;
}
