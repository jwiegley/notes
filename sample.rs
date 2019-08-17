use futures::future::*;
use futures::Future;

fn sample(
    xs: &dyn Future<Item = Vec<Box<dyn Future<Item = u32, Error = ()>>>, Error = ()>,
) -> impl Future<Item = Option<u32>, Error = ()> {
    xs.and_then(|resp: Vec<Box<dyn Future<Item = u32, Error = ()>>>>| {
        resp.into_iter().fold(
            Box::new(ok(None)),
            |acc: Box<dyn Future<Item = Option<u32>, Error = ()>>,
             x: Box<dyn Future<Item = u32, Error = ()>>| {
                acc.and_then(|val| {
                    if let Some(_) = val {
                        ok(Box::new(ok(val)))
                    } else {
                        ok(Box::new(x.and_then(move |resp: u32| ok(Some(resp)))))
                    }
                })
            },
        )
    })
}
