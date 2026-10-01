const api = [
  "constructor", "prototype", "apply", "call", "bind", "split", "join",
  "charCodeAt", "fromCharCode", "decodeURIComponent", "atob", "eval",
  "setTimeout", "replace", "substring", "toString"
];

const pool = [
  "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"
];

function decode(i) {
  return pool[(i ^ 3) & 7] +
    pool[(i + 1) & 7] +
    pool[(i + 2) & 7] +
    pool[(i + 3) & 7] +
    pool[(i + 4) & 7];
}

const chars = [72, 101, 108, 108, 111, 32, 102, 114, 111, 109, 32, 98, 121, 116, 101, 115, 33];
const assembled = String.fromCharCode(
  chars[0], chars[1], chars[2], chars[3], chars[4],
  chars[5], chars[6], chars[7], chars[8], chars[9]
);

const payload = "ZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KZnVuY3Rpb24gaGlkZGVuRGVjb2Rlcih4KXtyZXR1cm4geC5zcGxpdCgnJykucmV2ZXJzZSgpLmpvaW4oJycpO30KY29uc29sZS5sb2coaGlkZGVuRGVjb2RlcigncGF5bG9hZCcpKTsK";

const decoded = atob(payload);
const viaCall = decode(payload.length & 7);
const decoderNoise = decode(0x1f) + decode(0x20) + decode(0x21) + decode(0x22);
console.log(assembled, decoded.length, viaCall, decoderNoise, api[0]);
