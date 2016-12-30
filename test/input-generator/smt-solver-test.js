const path = require('path');
const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const expect = chai.expect;

chai.use(chaiAsPromised);

let testee = require('../../input-generator/smt-solver/index.js');

describe('SMT-Solver', () => {
	describe('SimpleMath Test Fixture', () => {
		let testResult;

		before(() => {
			const fixture = require(path.join(__dirname, '../fixtures/uml/SimpleMath.json'));
			const promise = testee(fixture);

			return expect(promise).to.be.fulfilled.then((result) => {
				expect(result.SimpleMath).to.be.an('object');
				testResult = result.SimpleMath;
			});
		});

		it('should describe 4 methods', () => {
			expect(testResult).to.be.an('object');
			expect(Object.keys(testResult)).to.have.length(4);
		});

		// it('should describe a "tests" Array on all methods', () => {
		// 	Object.keys(testResult).map((method) => {
		// 		expect(method.tests).to.be.instanceOf(Array);
		// 	});
		// });

		describe('SimpleMath#Add', () => {
			let method;

			before(() => {
				method = testResult.Add;
			});

			it('should describe a test case where all preconditions are satisfied', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						test.arguments.b >= 0;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 1 is not true', () => {
				const results = method.map((test) => {
					return !(test.arguments.a >= 0) &&
						test.arguments.b >= 0;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 2 is not true', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						!(test.arguments.b >= 0);
				});

				expect(results).to.include(true);
			});
		});

		describe('SimpleMath#Subtract', () => {
			let method;

			before(() => {
				method = testResult.Subtract;
			});

			it('should describe a test case where all preconditions are satisfied', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						test.arguments.b >= 0 &&
						test.arguments.a >= test.arguments.b;
				});

				expect(results).to.include(true);
			});

			it('should state forcing only precondition 1 not to true is unsatisfiable', () => {
				const results = method.map((test) => {
					return test.arguments === 'Unsatisfiable';
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 2 is not true', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						!(test.arguments.b >= 0) &&
						test.arguments.a >= test.arguments.b;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 3 is not true', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						test.arguments.b >= 0 &&
						!(test.arguments.a >= test.arguments.b);
				});

				expect(results).to.include(true);
			});
		});

		describe('SimpleMath#Divide', () => {
			let method;

			before(() => {
				method = testResult.Divide;
			});

			it('should describe a test case where all preconditions are satisfied', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						test.arguments.b > 0;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 1 is not true', () => {
				const results = method.map((test) => {
					return !(test.arguments.a >= 0) &&
						test.arguments.b > 0;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 2 is not true', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0 &&
						!(test.arguments.b > 0);
				});

				expect(results).to.include(true);
			});
		});

		describe('SimpleMath#SquareRoot', () => {
			let method;

			before(() => {
				method = testResult.SquareRoot;
			});

			it('should describe a test case where all preconditions are satisfied', () => {
				const results = method.map((test) => {
					return test.arguments.a >= 0;
				});

				expect(results).to.include(true);
			});

			it('should describe a test case where precondition 1 is not true', () => {
				const results = method.map((test) => {
					return !(test.arguments.a >= 0);
				});

				expect(results).to.include(true);
			});
		});
	});
});
