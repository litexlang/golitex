//! Finite and one-sided interval objects.

use crate::prelude::*;

#[derive(Clone)]
pub enum OneSideInfinityIntervalObj {
    LeftOpen(OneSideInfinityIntervalObjStruct),
    LeftClosed(OneSideInfinityIntervalObjStruct),
    RightOpen(OneSideInfinityIntervalObjStruct),
    RightClosed(OneSideInfinityIntervalObjStruct),
}

#[derive(Clone)]
pub struct OneSideInfinityIntervalObjStruct {
    pub start: Box<Obj>,
}

impl OneSideInfinityIntervalObjStruct {
    pub fn new(start: Obj) -> Self {
        OneSideInfinityIntervalObjStruct {
            start: Box::new(start),
        }
    }
}

impl OneSideInfinityIntervalObj {
    pub fn new_left_open(start: Obj) -> Self {
        OneSideInfinityIntervalObj::LeftOpen(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_left_closed(start: Obj) -> Self {
        OneSideInfinityIntervalObj::LeftClosed(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_right_open(start: Obj) -> Self {
        OneSideInfinityIntervalObj::RightOpen(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_right_closed(start: Obj) -> Self {
        OneSideInfinityIntervalObj::RightClosed(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn interval_struct(&self) -> &OneSideInfinityIntervalObjStruct {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(x)
            | OneSideInfinityIntervalObj::LeftClosed(x)
            | OneSideInfinityIntervalObj::RightOpen(x)
            | OneSideInfinityIntervalObj::RightClosed(x) => x,
        }
    }

    pub fn start(&self) -> &Obj {
        self.interval_struct().start.as_ref()
    }

    pub fn left_closed(&self) -> bool {
        matches!(self, OneSideInfinityIntervalObj::LeftClosed(_))
    }

    pub fn right_closed(&self) -> bool {
        matches!(self, OneSideInfinityIntervalObj::RightClosed(_))
    }

    pub fn left_bounded(&self) -> bool {
        matches!(
            self,
            OneSideInfinityIntervalObj::LeftOpen(_) | OneSideInfinityIntervalObj::LeftClosed(_)
        )
    }

    pub fn same_kind_as(&self, other: &OneSideInfinityIntervalObj) -> bool {
        matches!(
            (self, other),
            (
                OneSideInfinityIntervalObj::LeftOpen(_),
                OneSideInfinityIntervalObj::LeftOpen(_)
            ) | (
                OneSideInfinityIntervalObj::LeftClosed(_),
                OneSideInfinityIntervalObj::LeftClosed(_)
            ) | (
                OneSideInfinityIntervalObj::RightOpen(_),
                OneSideInfinityIntervalObj::RightOpen(_)
            ) | (
                OneSideInfinityIntervalObj::RightClosed(_),
                OneSideInfinityIntervalObj::RightClosed(_)
            )
        )
    }
}

#[derive(Clone)]
pub enum IntervalObj {
    LeftOpenRightOpen(IntervalObjStruct),
    LeftOpenRightClosed(IntervalObjStruct),
    LeftClosedRightOpen(IntervalObjStruct),
    LeftClosedRightClosed(IntervalObjStruct),
}

#[derive(Clone)]
pub struct IntervalObjStruct {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

impl IntervalObjStruct {
    pub fn new(start: Obj, end: Obj) -> Self {
        IntervalObjStruct {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl IntervalObj {
    pub fn new_left_open_right_open(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftOpenRightOpen(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_open_right_closed(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftOpenRightClosed(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_closed_right_open(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftClosedRightOpen(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_closed_right_closed(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftClosedRightClosed(IntervalObjStruct::new(start, end))
    }

    pub fn interval_struct(&self) -> &IntervalObjStruct {
        match self {
            IntervalObj::LeftOpenRightOpen(x)
            | IntervalObj::LeftOpenRightClosed(x)
            | IntervalObj::LeftClosedRightOpen(x)
            | IntervalObj::LeftClosedRightClosed(x) => x,
        }
    }

    pub fn start(&self) -> &Obj {
        self.interval_struct().start.as_ref()
    }

    pub fn end(&self) -> &Obj {
        self.interval_struct().end.as_ref()
    }

    pub fn left_closed(&self) -> bool {
        matches!(
            self,
            IntervalObj::LeftClosedRightOpen(_) | IntervalObj::LeftClosedRightClosed(_)
        )
    }

    pub fn right_closed(&self) -> bool {
        matches!(
            self,
            IntervalObj::LeftOpenRightClosed(_) | IntervalObj::LeftClosedRightClosed(_)
        )
    }
}
