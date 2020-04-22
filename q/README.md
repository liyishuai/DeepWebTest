# Protocol Q
## Specification
1. The server generates some arbitrary `data`, represented as one byte.
2. The server receives one byte `request` from a client.
3.
   - If `request == data`, then the server should respond with `1`, goto step 2.
   - If `request != data`, then the server should respond with `0`, goto step 2.
   - In either case, `data` remains unchanged from step 1.

## Testing
1. Maintain a client-side knowledge of `data`, whether it `is` or `is_not` equal
to some value.
2. Generate a random `request` and send it to the server.
3.
   - If the server responded with `1`, then `is_not[request]` should be `false`,
     and `is` should be either unknown or equal to `request`, otherwise report a
     violation; if `is` was unknown, then set it to `request`; goto step 2.
   - If the server responded with `0`, then `is` should be either unknown or
     different from `request`, otherwise report a violation; set
     `is_not[request]` to `true`; goto step 2.

## Implementation
- [`server.c`](server.c), a Q server.
- [`tester.c`](tester.c), a tester that interacts with a server and tells whether
  it conforms with Q protocol.

## Usage
1. `make server tester` builds the executables.
2. `./server` launches a server which listens to `localhost:8000`.
3. In another console, `./tester` runs a test against the server.

## Note
- Upon `bind: Address already in use`, try another port with
  `PORT=8001 ./server` and `PORT=8001 ./tester`.
