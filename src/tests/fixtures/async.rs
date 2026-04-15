extern crate tokio;
use std::future::Future;
use std::time::Duration;

mod trpl {
    use tokio::runtime::Runtime;
    pub(crate) use tokio::task::spawn as spawn_task;
    pub(crate) use tokio::time::sleep;

    pub fn block_on<F, R>(future: F) -> R
    where
        F: Future<Output = R>,
    {
        Runtime::new().unwrap().block_on(future)
    }
}

fn main() {
    trpl::block_on(async {
        trpl::spawn_task(async {
            for i in 1..10 {
                println!("hi number {i} from the first task!");
                trpl::sleep(Duration::from_millis(500)).await;
            }
        });

        for i in 1..5 {
            println!("hi number {i} from the second task!");
            trpl::sleep(Duration::from_millis(500)).await;
        }
    });
}
