open SkipruntimeCore

// Demonstrates notifier callbacks:
// 1) Create a notifier from the bindings.
// 2) Send collection updates to trigger notify callbacks.
// 3) Close the notifier and inspect the event log.
let () = {
  let events: array<string> = []

  let notifier =
    Notifier.make({
      // Note: `subscribed` is only triggered by runtime wiring (e.g., ServiceInstance.subscribe).
      // Here we call notify/close manually, so it won't fire.
      subscribed: () => events->Array.push("subscribed")->ignore,
      notify: update => {
        update.values->Array.forEach(((key, _vals)) =>
          events->Array.push(`notify:${JSON.stringify(key)}`)->ignore
        )
      },
      close: () => events->Array.push("close")->ignore,
    })

  // Initial update (isInitial=true) with one key; watermark marks batch position
  // so subscribers can track progress in a stream of updates.
  let update: collectionUpdate<JSON.t, JSON.t> = {
    values: [(JSON.String("k"), [JSON.Null])],
    watermark: "w0", // user-chosen batch identifier carried with the update
    isInitial: Some(true),
  }

  // Follow-up update with multiple keys in one batch (including updating an existing key).
  let update2: collectionUpdate<JSON.t, JSON.t> = {
    values: [
      (JSON.String("k2"), [JSON.Null]),
      (JSON.String("k3"), [JSON.String("v3")]),
      // Update existing key k with a new value to show repeat updates.
      (JSON.String("k"), [JSON.String("v-updated")]),
    ],
    watermark: "w1",
    isInitial: None,
  }

  notifier->Notifier.notify(update)
  notifier->Notifier.notify(update2)
  notifier->Notifier.close

  Console.log2("notifier events", events)
}