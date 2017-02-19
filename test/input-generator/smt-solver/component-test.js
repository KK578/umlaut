const testee = require('../../../input-generator/smt-solver/index.js');

describe('SimpleMath Test Fixture', function () {
	let testResult;

	before(function () {
		const fixture = require(global.fixtures.FullModels.SimpleMath['uml-parser']);
		const promise = testee(fixture);

		return expect(promise).to.be.fulfilled.then((result) => {
			expect(result.SimpleMath).to.be.an('object');
			testResult = result.SimpleMath;
		});
	});

	it('should describe 4 methods', function () {
		expect(testResult).to.be.an('object');
		expect(Object.keys(testResult)).to.have.length(4);
	});

	describe('SimpleMath#Add', function () {
		let method;

		before(function () {
			method = testResult.Add;
		});

		it('should describe a test case where all preconditions are satisfied', function () {
			const results = method.map((test) => {
				return test.arguments.a >= 0 &&
					test.arguments.b >= 0;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 1 is not true', function () {
			const results = method.map((test) => {
				return !(test.arguments.a >= 0) &&
					test.arguments.b >= 0;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 2 is not true', function () {
			const results = method.map((test) => {
				return test.arguments.a >= 0 &&
					!(test.arguments.b >= 0);
			});

			expect(results).to.include(true);
		});
	});

	describe('SimpleMath#Subtract', function () {
		let method;

		before(function () {
			method = testResult.Subtract;
		});

		it('should describe a test case where all preconditions are satisfied', function () {
			const results = method.map((test) => {
				if (test.unsatisfiable) {
					return false;
				}

				return test.arguments.a >= 0 &&
					test.arguments.b >= 0 &&
					test.arguments.a >= test.arguments.b;
			});

			expect(results).to.include(true);
		});

		it('should state forcing only precondition 1 not to true is unsatisfiable', function () {
			const results = method.map((test) => {
				return test.unsatisfiable;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 2 is not true', function () {
			const results = method.map((test) => {
				if (test.unsatisfiable) {
					return false;
				}

				return test.arguments.a >= 0 &&
					!(test.arguments.b >= 0) &&
					test.arguments.a >= test.arguments.b;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 3 is not true', function () {
			const results = method.map((test) => {
				if (test.unsatisfiable) {
					return false;
				}

				return test.arguments.a >= 0 &&
					test.arguments.b >= 0 &&
					!(test.arguments.a >= test.arguments.b);
			});

			expect(results).to.include(true);
		});
	});

	describe('SimpleMath#Divide', function () {
		let method;

		before(function () {
			method = testResult.Divide;
		});

		it('should describe a test case where all preconditions are satisfied', function () {
			const results = method.map((test) => {
				return test.arguments.a >= 0 &&
					test.arguments.b > 0;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 1 is not true', function () {
			const results = method.map((test) => {
				return !(test.arguments.a >= 0) &&
					test.arguments.b > 0;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 2 is not true', function () {
			const results = method.map((test) => {
				return test.arguments.a >= 0 &&
					!(test.arguments.b > 0);
			});

			expect(results).to.include(true);
		});
	});

	describe('SimpleMath#SquareRoot', function () {
		let method;

		before(function () {
			method = testResult.SquareRoot;
		});

		it('should describe a test case where all preconditions are satisfied', function () {
			const results = method.map((test) => {
				return test.arguments.a >= 0;
			});

			expect(results).to.include(true);
		});

		it('should describe a test case where precondition 1 is not true', function () {
			const results = method.map((test) => {
				return !(test.arguments.a >= 0);
			});

			expect(results).to.include(true);
		});
	});
});
