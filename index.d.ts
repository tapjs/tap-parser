export interface Plan {
  start: number;
  end: number;
  skipAll: boolean;
  skipReason: string;
  comment: string;
}

export interface Result {
  ok: boolean;
  id: number;
  name: string;
  fullname: string;
}

export interface Results {
  ok: boolean;
  count: number;
  pass: number;
  fail: number;
  bailout: false | string;
  todo: number;
  skip: number;
  plan: Plan;
  failures: Result[];
}

export default class Parser {
  end(chunk: string): void;
  on(event: 'complete', cb: (results: Results) => void): void;
}
