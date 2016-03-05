#![feature(box_patterns)]
#![feature(box_syntax)]

use std::ops::{Mul, Add, Div, Sub, Neg, BitXor};
use std::convert::From;

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
            Add(box f, box g) => f.derivative() + g.derivative(),
            Const(n) => Const(n),
            Constrainted(box f, con) => f.derivative().rule(con),
            Ln(box f) => f.clone().derivative() * f.rule(Positive).rule(NonOne),
            Mul(box f, box g) => f.clone().derivative() * g.clone() + f * g.derivative(),
            Neg(box f) => -f.derivative(),
            Pow(box f, box g) => (f.clone() ^ g.clone()) * f.clone().derivative() * g.clone() / f.clone() + g.derivative() * f.ln(),
            Rec(box f) => -f.clone().derivative().rule(NonZero) / f.clone() / f,
            Var(_) => Const(0.0),
            X => Const(1.0),
        }
    }

    fn ln(self) -> Func {
        Func::Ln(box self)
    }

    fn rule(self, c: Constraint) -> Func {
        Func::Constrainted(box self, c)
    }

    pub fn to_string(&self) -> String {
        use Func::*;

        match self {
            &Add(ref a, ref b) => format!("({} + {})", a.to_string(), b.to_string()),
            &Const(n) => n.to_string(),
            &Constrainted(ref a, _) => a.to_string(),
            &Ln(ref a) => format!("ln({})", a.to_string()),
            &Mul(ref a, ref b) => format!("({} * {})", a.to_string(), b.to_string()),
            &Neg(ref a) => format!("(-{})", a.to_string()),
            &Pow(ref a, ref b) => format!("{} ^ {}", a.to_string(), b.to_string()),
            &Rec(ref a) => format!("(1 / {})", a.to_string()),
            &Var(_) => "_".to_owned(),
            &X => "x".to_owned(),
        }
    }
}

#[test]
fn test_derivative() {
    use Func::*;
    let f = X ^ X * 3.0.into();

    assert_eq!(&f.derivative().to_string(), "((((x ^ (x * 3) * 1) * (x * 3)) * (1 / x)) + (((1 * 3) + (x * 3)) * ln(x)))"); // (X ^ X) * (Const(1.0) + X.ln()) * Const(3.0))
}
