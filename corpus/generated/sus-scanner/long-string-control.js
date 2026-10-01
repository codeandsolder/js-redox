export function describeRequest(request) {
  return "method=" + request.method
    + " url=" + request.url
    + " status=" + request.status
    + " elapsed=" + request.elapsed
    + " cache=" + request.cache
    + " protocol=" + request.protocol
    + " host=" + request.host
    + " path=" + request.path
    + " query=" + request.query
    + " referrer=" + request.referrer
    + " userAgent=" + request.userAgent
    + " retries=" + request.retries
    + " region=" + request.region
    + " edge=" + request.edge
    + " trace=" + request.trace;
}

console.log(describeRequest({
  method: "GET",
  url: "/",
  status: 200,
  elapsed: 12,
  cache: "hit",
  protocol: "https",
  host: "example.test",
  path: "/",
  query: "",
  referrer: "",
  userAgent: "fixture",
  retries: 0,
  region: "test",
  edge: "local",
  trace: "abc"
}));
