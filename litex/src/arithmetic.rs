// Evaluate implementations
use crate::errors::ArithmeticErr;
use crate::obj::Obj;
use crate::obj::{Add, Div, Mod, Mul, Number, Pow, Sub};


fn num_value(obj: &Obj) -> f64 {
    match obj {
        Obj::Number(n) => n.value.parse().unwrap_or(0.0),
        _ => 0.0,
    }
}

impl Obj {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        match self {
            Obj::Number(n) => Ok(Obj::Number(Number { value: n.value.clone() })),
            Obj::Add(a) => a.calculate(),
            Obj::Sub(s) => s.calculate(),
            Obj::Mul(m) => m.calculate(),
            Obj::Div(d) => d.calculate(),
            Obj::Mod(m) => m.calculate(),
            Obj::Pow(p) => p.calculate(),
            _ => Err(ArithmeticErr::new("非算术表达式，无法 calculate")),
        }   
    }
}

impl Add {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }
        
        let l = self.left.as_ref().calculate();
        if l.is_err() {
            return l;
        }
        let r = self.right.as_ref().calculate();
        if r.is_err() {
            return r;
        }
        let v = num_value(&l.unwrap()) + num_value(&r.unwrap());
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}

impl Sub {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }   
        
        let l = self.left.as_ref().calculate();
        if l.is_err() {
            return l;
        }
        let r = self.right.as_ref().calculate();
        if r.is_err() {
            return r;
        }
        let v = num_value(&l.unwrap()) - num_value(&r.unwrap());
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}

impl Mul {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.as_ref().calculate();
        if l.is_err() {
            return l;
        }
        let r = self.right.as_ref().calculate();
        if r.is_err() {
            return r;
        }
        let v = num_value(&l.unwrap()) * num_value(&r.unwrap());
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}

impl Div {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.as_ref().calculate();
        if l.is_err() {
            return l;
        }
        let r = self.right.as_ref().calculate();
        if r.is_err() {
            return r;
        }
        let v = num_value(&l.unwrap()) / num_value(&r.unwrap());
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}

impl Mod {
    pub fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.as_ref().calculate();
        if l.is_err() {
            return l;
        }
        let r = self.right.as_ref().calculate();
        if r.is_err() {
            return r;
        }
        let v = num_value(&l.unwrap()) % num_value(&r.unwrap());
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}

impl Pow {
    fn calculate(&self) -> Result<Obj, ArithmeticErr> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticErr::new("非算术表达式，无法 calculate"));
        }
        let b = self.base.as_ref().calculate();
        if b.is_err() {
            return b;
        }
        let e = self.exponent.as_ref().calculate();
        if e.is_err() {
            return e;
        }
        let v = num_value(&b.unwrap()).powf(num_value(&e.unwrap()));
        Ok(Obj::Number(Number { value: v.to_string() }))
    }
}