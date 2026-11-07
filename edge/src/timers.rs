//! The kernel's timers: a min-heap of deadlines keyed by the kernel's ids.
//! Starting an id again moves it; cancelled or moved entries stay in the heap
//! and are skipped when they surface.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::time::{Duration, Instant};

#[derive(Default)]
pub struct Timers {
    heap: BinaryHeap<Reverse<(Instant, u32)>>,
    due: HashMap<u32, Instant>,
}

impl Timers {
    pub fn start(&mut self, id: u32, ms: u32, now: Instant) {
        let at = now + Duration::from_millis(ms as u64);
        self.due.insert(id, at);
        self.heap.push(Reverse((at, id)));
    }

    pub fn cancel(&mut self, id: u32) {
        self.due.remove(&id);
    }

    /// The earliest live deadline, dropping the dead entries above it.
    pub fn deadline(&mut self) -> Option<Instant> {
        while let Some(Reverse((at, id))) = self.heap.peek() {
            if self.due.get(id) == Some(at) {
                return Some(*at);
            }
            self.heap.pop();
        }
        None
    }

    /// The id of one timer due at `now`, taken out.
    pub fn pop_due(&mut self, now: Instant) -> Option<u32> {
        let at = self.deadline()?;
        if at > now {
            return None;
        }
        let Reverse((_, id)) = self.heap.pop()?;
        self.due.remove(&id);
        Some(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    #[test]
    fn fires_in_deadline_order() {
        let t0 = Instant::now();
        let mut t = Timers::default();
        t.start(1, 30, t0);
        t.start(2, 10, t0);
        t.start(3, 20, t0);
        assert_eq!(t.deadline(), Some(t0 + ms(10)));
        assert_eq!(t.pop_due(t0 + ms(5)), None);
        assert_eq!(t.pop_due(t0 + ms(25)), Some(2));
        assert_eq!(t.pop_due(t0 + ms(25)), Some(3));
        assert_eq!(t.pop_due(t0 + ms(25)), None);
        assert_eq!(t.pop_due(t0 + ms(30)), Some(1));
        assert_eq!(t.deadline(), None);
    }

    #[test]
    fn cancel_and_restart_forget_the_old_deadline() {
        let t0 = Instant::now();
        let mut t = Timers::default();
        t.start(1, 10, t0);
        t.cancel(1);
        assert_eq!(t.deadline(), None);
        t.start(1, 10, t0);
        t.start(1, 40, t0);
        assert_eq!(t.pop_due(t0 + ms(20)), None);
        assert_eq!(t.pop_due(t0 + ms(40)), Some(1));
        assert_eq!(t.pop_due(t0 + ms(100)), None);
    }
}
