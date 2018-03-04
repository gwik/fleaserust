// BJORN KOLBECK, MIKAEL HOGQVIST, JAN STENDER, FELIX HUPFELD
// Fault-tolerant and Decentralized Lease Coordination in Distributed Systems

// Module rbr defines round-based distributed registers.
pub mod rbr {

	use std::cmp::{Ord};
	use std::marker::{Copy};

    // Register represents a round-based distributed register a defined in the
    // Paxos paper.
    #[derive(Debug)]
	pub struct Register<K, V> { // XXX(gwik) is it needed to expose it ?
		read_at: K,
		written_at: K,
		val: Option<V>,
	}

    // ReadValue is the return value of the read operation.
    #[derive(Debug, Copy, Clone)]
	pub struct ReadValue<K, V> {
		pub written_at: K,
		pub val: Option<V>,
	}

	impl <K: Ord + Copy, V: Clone> Register<K, V> {

		// empty initialize an empty register with k read and write K.
		pub fn empty(k: K) -> Register<K, V> {
			Register{
				read_at: k,
				written_at: k,
				val: None,
			}
		}

		// read reads the register value and returns a non-None optional on
		// success.
        //
        // Lemma R1. Read-abort: If read(k) aborts, then some operation read(k')
        // or write(k', *) was invoked with k' >= k.
		pub fn read(&mut self, k: K) -> Option<ReadValue<K, V>> {
			if self.written_at >= k || self.read_at >= k {
				None
			} else {
				self.read_at = k;
				Some(ReadValue{written_at: self.written_at, val: self.val.clone()})
			}
		}

		// write writes val to the register and return if it succeeded.
        //
        // Lemma R2. Write-abort: If write(k,*) aborts,then some operation
        // read(k') or write(k', *) was invoked with k0 > k.
        //
        // Lemma R3. Read-write-commit: If read(k) or write(k,*) commits, then
        // no subsequent read(k') can commit with k' <= k or write(k'',*) can
        // commit with k'' <= k.
		pub fn write(&mut self, k: K, v: &V) -> Option<()> {
            // TODO(gwik): consider taking &V and clone on success only.

			if self.written_at > k || self.read_at > k {
				None
			} else {
				self.written_at = k;
				self.val = Some(v.clone());
				Some(())
			}
		}
	}

    pub mod distributed {
        use super::{ReadValue};
        use std::vec::{Vec};
        use std::result::{Result};
        use std::io;
        use std::time::{Duration};

        pub type NodeId = u32;

        #[derive(Debug)]
        pub enum Failure {
            Abort,
            Error(io::Error),
        }

        pub trait RPC<'a, K: 'a, V: 'a> {
            fn read(&'a self, K, timeout: Duration) -> Result<ReadValue<K, V>, Failure>;
            fn write(&'a self, K, &V, timeout: Duration) -> Result<(), Failure>;
        }

        pub trait Node<'a, K: 'a, V: 'a>: RPC<'a, K, V> {
            fn id(&self) -> NodeId;
        }
 
        pub struct Cluster<'a, K: 'a, V: 'a> {
            nodes: Vec<&'a Node<'a, K, V>>,
        }

        impl<'a, K: Ord + Copy, V: Clone> Cluster<'a, K, V> {

            pub fn new(nodes: Vec<&'a Node<'a, K, V>>) -> Cluster<K, V> {
                Cluster{nodes: nodes}
            }

        }

        impl<'a, 'b, K: Ord + Copy, V: Clone> Cluster<'b, K, V> {

            // propose writes the value v with ballot k and returns the value of
            // the register. Register implements a write-once semantic and the
            // value of a successful propose is v or the already set value of
            // the register.
            pub fn propose(&self, k: K, v: V, timeout: Duration) -> Result<V, Failure> {
                let v = match self.read(k, timeout) {
                    Ok(rval) => match rval.val {
                        Some(existing_value) => existing_value,
                        None => v,
                    },
                    Err(failure) => return Err(failure),
                };

                match self.write(k, &v, timeout) {
                    Ok(()) => {},
                    Err(failure) => return Err(failure),
                };

                Ok(v)
            }

            pub fn read(&self, k: K, timeout: Duration) -> Result<ReadValue<K, V>, Failure> {
                let len = self.nodes.len() as isize;
                let mut quorum =  1 + len / 2;
                let mut errors =  len - quorum + 1;
                let mut rval : Option<ReadValue<K, V>> = None;
                let mut error : Failure = Failure::Abort;

                for node in self.nodes.iter() {
                    let nval : Result<Option<ReadValue<K, V>>, Failure> = {
                        match node.read(k, timeout) {
                            Ok(node_rval) => {
                                match rval {
                                    Some(ref rv) => {
                                        if rv.written_at < node_rval.written_at {
                                           Ok(Some(node_rval))
                                        } else {
                                           Ok(None)
                                        }
                                    },
                                    None => {
                                        Ok(Some(node_rval))
                                    }
                                }
                            },
                            Err(e) => Err(e),
                        }
                    };

                    match nval {
                        Ok(ov) => {
                            quorum -= 1;
                            match ov {
                                Some(rv) => {
                                    rval = Some(rv)
                                },
                                None => {},
                            }
                        },
                        Err(Failure::Abort) => return Err(Failure::Abort),
                        Err(e) => {
                            errors -= 1;
                            error = e;
                        },
                    }

                    if errors <= 0 || quorum <= 0 {
                        break
                    }
                }

                if quorum <= 0 {
                    match rval {
                        Some(v) => return Ok(v),
                        None => return Err(error),
                    }
                }
                return Err(error)
            }

            pub fn write(&self, k: K, v: &V, timeout: Duration) -> Result<(), Failure> {
                let len = self.nodes.len() as isize;
                let mut quorum =  1 + len / 2;
                let mut errors =  len - quorum + 1;
                let mut error : Failure = Failure::Abort;

                for node in self.nodes.iter() {
                    match node.write(k, v, timeout) {
                        Ok(()) => {
                            quorum -= 1;
                        },
                        Err(Failure::Abort) => {
                            return Err(Failure::Abort);
                        },
                        Err(Failure::Error(e)) => {
                            errors -= 1;
                            error = Failure::Error(e)
                        },
                    }

                    if errors <= 0 || quorum <= 0 {
                        break
                    }
                }

                if quorum <= 0 {
                    return Ok(())
                }
                return Err(error)
            }
        }
    }
}

pub mod flease {
    use std::time::{Instant, Duration};
    use rbr::distributed::{Cluster, NodeId, Failure};
    use std::thread;
    use std::cmp::Ordering;

    #[derive(Debug, Copy, Clone, Eq)]
    pub struct K {
        instant: Instant,
        node_id: NodeId,
        rand: i64,
    }

    impl K {
        pub fn new(instant: Instant, node_id: NodeId, rand: i64) -> K {
            K{instant, node_id, rand}
        }

        pub fn as_tuple(&self) -> (Instant, NodeId, i64) {
            (self.instant, self.node_id, self.rand)
        }
    }

    // TODO(gwik): implement comparator for K : 
    // "We consider time-ranges for comparison rather than just the timestamps.
    // As long as |t - t'| <= epsilon, we consider the messages to be equal and
    // use the process id and a random value to distinguish the messages."

    impl PartialEq for K {
        fn eq(&self, other: &K) -> bool {
            self.as_tuple() == other.as_tuple()
        }
    }

    impl Ord for K {
        fn cmp(&self, other: &K) -> Ordering {
            self.as_tuple().cmp(&other.as_tuple())
        }
    }

    impl PartialOrd for K {
        fn partial_cmp(&self, other: &K) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    #[derive(Debug, Copy, Clone)]
    pub struct Lease {
        pub owner: NodeId,
        pub expire: Instant,
    }

    pub struct Leaser<'a> {
        id: NodeId, // p_i
        cluster: &'a Cluster<'a, K, Lease>,

        drift_max: Duration, // epsilon
        lease_max: Duration, // t_max
    }

    impl<'a, 'b> Leaser<'a> {

        pub fn new(id: NodeId, cluster: &'b Cluster<'b, K, Lease>, lease_max: Duration, drift_max: Duration) -> Leaser {
            return Leaser{id: id, cluster: cluster, lease_max: lease_max, drift_max: drift_max}
        }

        pub fn get_lease(&'a self, rand: i64, timeout: Duration) -> Result<Lease, Failure> {
            // TODO(gwik): deadline is probably more appropriate for this recursive function.

            let k = K{instant: Instant::now(), node_id: self.id, rand: rand};
            let lease_opt = match self.cluster.read(k, timeout) {
                Ok(rval) => rval.val,
                Err(failure) => return Err(failure),
            };

            let now = Instant::now();
            let lease = match lease_opt {
                Some(lease) => {
                    if lease.expire < now && lease.expire + self.drift_max > now {
                        // TODO(gwik): do not sleep longer than available time from deadline.
                        thread::sleep(self.drift_max);
                        return self.get_lease(rand, timeout)
                    }

                    if lease.expire < now || lease.owner == self.id {
                        Lease{expire: now + self.lease_max, owner: self.id}
                    } else {
                        lease
                    }
                },
                None => Lease{expire: now + self.lease_max, owner: self.id},
            };

            match self.cluster.write(k, &lease, timeout) {
                Ok(()) => Ok(lease),
                Err(failure) => Err(failure),
            }
        }

    }
}

// channel_rpc implements rbr::distributed::RPC with channels.
pub mod channel_rpc {

    use rbr::distributed::{Failure, NodeId, Node, RPC};
    use rbr::{Register, ReadValue};
    use std::sync::mpsc::{Sender, Receiver, channel};
    use std::thread;
    use std::time::{Duration};

    #[derive(Debug, Clone)]
    enum Request<K, V> {
        Read(K),
        Write((K, V)),
        Halt,
    }

    enum Reply<K, V> {
        Read(Result<ReadValue<K, V>, Failure>),
        Write(Result<(), Failure>),
    }

    pub struct ChanNode<K, V> {
        id: NodeId,
        thread: Option<thread::JoinHandle<()>>,
        tx: Sender<(Request<K, V>, Sender<Reply<K, V>>)>,
    }

    impl<K, V> Clone for ChanNode<K, V> {
        fn clone(&self) -> ChanNode<K, V> {
            ChanNode{id: self.id, thread: None, tx: self.tx.clone()}
        }
    }

    impl<K: Ord + Copy + Send + 'static, V: Clone + Send + Sync + 'static> ChanNode<K, V> {

        pub fn new(id: NodeId, k0: K) -> ChanNode<K, V> {
            let (tx, rx): (
                Sender<(Request<K, V>, Sender<Reply<K, V>>)>,
                Receiver<(Request<K, V>, Sender<Reply<K, V>>)>,
            ) = channel();

            let t = thread::spawn(move || {
                let mut reg = Register::empty(k0);
                let (req, tx) = match rx.recv() {
                    Ok(a) => a,
                    Err(e) => { println!("recv error {:}", e); return },
                };
                let reply = match req {
                    Request::Read(k) => match reg.read(k) {
                        Some(rval) => Reply::Read(Ok(rval)),
                        None => Reply::Read(Err(Failure::Abort)),
                    },
                    Request::Write((k, v)) => match reg.write(k, &v) {
                        Some(()) => Reply::Write(Ok(())),
                        None => Reply::Write(Err(Failure::Abort)),
                    },
                    Request::Halt => return,
                };
                match tx.send(reply) {
                    Ok(a) => a,
                    Err(e) => { println!("send error {:}", e); return },
                }
            });

            ChanNode{id: id, tx: tx, thread:Some(t)}
        }

    }

    impl<K, V> Drop for ChanNode<K, V> {
        fn drop(&mut self) {
            let (tx, _) : (Sender<Reply<K, V>>, Receiver<Reply<K, V>>) = channel();
            match self.tx.send((Request::Halt, tx.clone())) {
                Ok(_) => {},
                Err(e) => println!("drop send error node={:} err={:}", self.id, e),
            }
            if let Some(thread) = self.thread.take() {
                thread.join().unwrap();
            }
        }
    }

    impl<'a, K: Ord + Copy + Send + 'a, V: Clone + Send + 'a> RPC<'a, K, V> for ChanNode<K, V> {

        fn read(&'a self, k: K, _timeout: Duration) -> Result<ReadValue<K, V>, Failure> {
            let (tx, rx) : (Sender<Reply<K, V>>, Receiver<Reply<K, V>>) = channel();
            self.tx.send((Request::Read(k), tx.clone())).unwrap();
            let reply = rx.recv().unwrap();
            match reply {
                Reply::Read(res) => res,
                _ => unreachable!(),
            }
        }

        fn write(&'a self, k: K, v: &V, _timeout: Duration) -> Result<(), Failure> {
            let (tx, rx) : (Sender<Reply<K, V>>, Receiver<Reply<K, V>>) = channel();
            let v = v.clone();
            self.tx.send((Request::Write((k, v)), tx.clone())).unwrap(); // TODO(gwik): io::Error on Err
            let reply = rx.recv().unwrap(); // TODO(gwik): io::Error on Err
            match reply {
                Reply::Write(res) => res,
                _ => unreachable!(),
            }
        }

    }

    impl<'a, K: Ord + Copy + Send + 'a, V: Clone + Send + 'a> Node<'a, K, V> for ChanNode<K, V> {
        fn id(&self) -> NodeId {
            return self.id
        }
    }

}

#[cfg(test)]
mod tests {
    use std::time::{Instant, Duration};
    use std::result::{Result};
    use std::cell::{RefCell};
    use std::sync::{Mutex};

    use rbr::*;
    use rbr::distributed::*;

    #[test]
    fn register_read_write_value() {
    	let now = Instant::now();
        let mut reg : Register<Instant, i32> = Register::empty(now);

        assert!(reg.read(now).is_none(), "read with same k the register was created must fail");

        // This can be suprising at first. But this is straightforward once you
        // consider this is a distributed register. If no other process
        // succesfully read the value then the write can happen.
        assert_eq!(reg.write(now, &1).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, &2).is_none(), false, "write with the same k must succeed");
        assert_eq!(reg.write(now, &3).is_none(), false, "write with the same k must succeed");

        let later = now + Duration::from_millis(1);
        {
            let read = reg.read(later);
            assert_eq!(read.is_none(), false, "read must succeed with a later timestamp");
            let rval = read.unwrap();

            assert_eq!(rval.written_at, now);
            assert_eq!(rval.val.unwrap(), 3);
        }

        assert!(reg.read(later).is_none(), "read with same read k must fail");
        assert!(reg.read(now).is_none(), "read with an older k must fail");

        assert_eq!(reg.write(now, &10).is_none(), true, "write with a later k must fail");
        assert_eq!(reg.write(later, &1).is_none(), false, "write with a later k must fail");
    }

    struct TestOKNode<'a, K: 'a, V: 'a> {
        id:  u32,
        // ???(gwik): Arc / Rc is often mentioned with RefCell.. what would be the point ?
        reg: Mutex<&'a RefCell<Register<K, V>>>,
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> TestOKNode<'a, K, V> {
        fn new(id: u32, reg: &'a RefCell<Register<K,V>>) -> TestOKNode<'a, K, V> {
            TestOKNode{id: id, reg: Mutex::new(reg)}
        }
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> Node<'a, K, V> for TestOKNode<'a, K, V> {
        fn id(&self) -> u32 {
            self.id
        }
    }

    impl<'a, K: Ord + Copy + 'a, V: Clone + 'a> RPC<'a, K, V> for TestOKNode<'a, K, V> {
        fn read(&'a self, k: K, _timeout: Duration) -> Result<ReadValue<K, V>, Failure> {
            match self.reg.lock().unwrap().borrow_mut().read(k) {
                Some(rval) => Ok(rval),
                None => Err(Failure::Abort),
            }
        }

        fn write(&'a self, k: K, v: &V, _timeout: Duration) -> Result<(), Failure> {
            match self.reg.lock().unwrap().borrow_mut().write(k, v) {
                Some(()) => Ok(()),
                None => Err(Failure::Abort),
            }
        }
    }

    // ???(gwik) how to write a constructor for node
    // since register would not outlive the scope of the method.
    // is it even possible ?
    // e.g:
    // fn new(id, k) Node<i32,i64> {
    //     let reg = RefCell::new(Register<...>); // would be destroyed at the end of the scope.
    // }

    #[test]
    fn cluster_read() {

        let k = 0i32;
        let regs : Vec<RefCell<Register<i32, i64>>> = vec![
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
        ];

        let nodes : Vec<TestOKNode<i32, i64>> = regs.iter()
            .enumerate()
            .map(|(i, r)| TestOKNode::new(i as u32, &r))
            .collect();

        let cluster = Cluster::new(nodes
            .iter()
            .map(|n| n as &Node<i32, i64>)
            .collect());

        let timeout = Duration::from_secs(10);

        {
            assert!(cluster.read(1i32, timeout).is_ok());
        }
        {
            assert!(cluster.read(1i32, timeout).is_err());
        }
        {
            assert!(cluster.read(2i32, timeout).is_ok());
        }
        {
            let k = 3i32;
            regs[0].borrow_mut().read(k);

            let res = cluster.read(k, timeout);
            assert!(res.is_err());
            match res.err() {
                Some(Failure::Abort) => {},
                Some(Failure::Error(_e)) => assert!(false, "unexpected error"),
                None => unreachable!(),
            }
        }
    }

    #[test]
    fn cluster_propose() {
        let k = 0i32;
        let timeout = Duration::from_secs(10);
        let regs : Vec<RefCell<Register<i32, i64>>> = vec![
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
            { let k = k; RefCell::new(Register::empty(k)) },
        ];

        let nodes : Vec<TestOKNode<i32, i64>> = regs.iter()
            .enumerate()
            .map(|(i, r)| TestOKNode::new(i as u32, &r))
            .collect();

        let cluster = Cluster::new(nodes
            .iter()
            .map(|n| n as &Node<i32, i64>)
            .collect());

        let pres = cluster.propose(1, 1, timeout);
        assert!(pres.is_ok());
        assert_eq!(pres.unwrap(), 1);

        let pres = cluster.propose(2, 2, timeout);
        assert!(pres.is_ok());
        assert_eq!(pres.unwrap(), 1);

        let pres = cluster.propose(1, 2, timeout);
        assert!(pres.is_err());
        match pres.err() {
            Some(Failure::Abort) => {},
            _ => unreachable!(),
        }

    }


    #[test]
    fn channel_rpc() {
        use std::time::Duration;
        use std::thread;
        use std::time::Instant;

        use rbr::distributed::{Node, Cluster};
        use channel_rpc::ChanNode;
        use flease::*;

        let now = Instant::now();
        let nodes: Vec<ChanNode<K, Lease>> = vec![
            ChanNode::new(0, K::new(now, 0, 0)),
            ChanNode::new(1, K::new(now, 0, 0)),
            ChanNode::new(2, K::new(now, 0, 0)),
            ChanNode::new(3, K::new(now, 0, 0)),
            ChanNode::new(4, K::new(now, 0, 0)),
            ChanNode::new(5, K::new(now, 0, 0)),
        ];

        let mut threads : Vec<thread::JoinHandle<()>> = vec![];
        for id in nodes.iter().map(|n| n.id()) {
            let nodes : Vec<ChanNode<K, Lease>> = nodes.iter().map(|n| (*n).clone()).collect();
            let handle = thread::spawn(move ||{

                thread::sleep(Duration::from_millis(1));

                let cluster = Cluster::new(nodes
                    .iter()
                    .map(|n| n as &Node<K, Lease>)
                    .collect());

                thread::sleep(Duration::from_millis(1));

                let leaser = Leaser::new(
                    id, &cluster, Duration::from_secs(10), Duration::from_secs(2));

                thread::sleep(Duration::from_millis(1));

                leaser.get_lease(id as i64, Duration::from_secs(5));
            });
            threads.push(handle);
        }

        for t in threads {
            t.join().unwrap()
        }

    }

    // TODO(gwik)
    //
    // - implement a RPC with TPC sockets (or UDP) and futures
    //   for UDP protocol needs to account for duplicate messages.

}
