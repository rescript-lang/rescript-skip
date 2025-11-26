open SkipruntimeCore

let () = {
  let status = LoadStatus.fromJs(2)
  Console.log2("status", status)

  let ex = Errors.nonUniqueValue("boom")
  Console.log2("error message", JsExn.message(ex))

  let back = LoadStatus.toJs(#incompatible)
  Console.log2("status back to js", back)

  let mapperClass =
    Natural.Mapper.make((_key, _values, _ctx, _params) => [
      (JSON.String("k"), JSON.Null),
    ])
  Console.log2("mapper class", mapperClass)

  let doubledMapper =
    Natural.Mapper.make((key, values, _ctx, _params) =>
      Values.toArray(values)->Array.map(v =>
        switch v {
        | JSON.Number(n) => (key, JSON.Number(n *. 2.))
        | _ => (key, v)
        }
      )
    )

  let sumReducer =
    Natural.Reducer.make(
      ~initial=_params => Some(JSON.Number(0.)),
      ~add=(acc, value, _params) =>
        switch (acc, value) {
        | (JSON.Number(total), JSON.Number(n)) => JSON.Number(total +. n)
        | _ => acc
        },
    )

  Console.log2("doubled mapper", doubledMapper)
  Console.log2("sum reducer", sumReducer)
}
