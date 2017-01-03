const path = require('path');

const promises = require('../../util/promises.js');
const REGEX_UUID = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

const testee = require('../../uml-parser/parsers/visual-studio/index.js');

describe('Visual Studio Parser', function () {
	it('should state it cannot parse a non XML string', function () {
		const notXml = 'FooBar';
		const promise = testee.detect(notXml);

		return expect(promise).to.be.fulfilled.then((result) => {
			expect(result).to.not.be.ok;
		});
	});

	it('should state it cannot parse an arbitrary XML string', function () {
		const notModelXml = '<foo><bar id="bar"></bar</foo>';
		const promise = testee.detect(notModelXml);

		return expect(promise).to.be.fulfilled.then((result) => {
			expect(result).to.not.be.ok;
		});
	});

	it('should state it can parse if the XML root contains a "modelStoreModel" node', function () {
		const modelXml = '<modelStoreModel></modelStoreModel>';
		const promise = testee.detect(modelXml);

		return expect(promise).to.be.fulfilled.then((result) => {
			expect(result).to.be.ok;
		});
	});

	it('should state it can parse if the XML root contains a "logicalClassDesignerModel" node', function () {
		const modelXml = '<logicalClassDesignerModel></logicalClassDesignerModel>';
		const promise = testee.detect(modelXml);

		return expect(promise).to.be.fulfilled.then((result) => {
			expect(result).to.be.ok;
		});
	});

	it('should parse Visual Studio model with class with no variables');
	it('should parse Visual Studio model with class with no methods');
	it('should parse Visual Studio model with no classes');
	it('should parse Visual Studio model with multiple classes');

	function simpleMathTestSuite(fixture) {
		let testResult;

		it('should successfully be detected as parsable', function () {
			return promises.fsReadFile(fixture).then((data) => {
				const promise = testee.detect(data);

				return expect(promise).to.be.fulfilled;
			}).then((result) => {
				expect(result).to.be.ok;
			});
		});

		it('should successfully be parsed', function () {
			return promises.fsReadFile(fixture).then((data) => {
				const promise = testee.parse(data);

				return expect(promise).to.be.fulfilled;
			}).then((result) => {
				expect(result.SimpleMath).to.be.an('object');
				testResult = result.SimpleMath;
			});
		});

		describe('Variables', function () {
			it('should contain a single variable "Nop"', function () {
				const variable = testResult.variables.Nop;

				expect(variable).to.be.an('object');
				expect(variable.id).to.be.a('string').and.match(REGEX_UUID);
				expect(variable.visibility).to.equal('Private');
				expect(variable.type).to.equal('Integer');
			});
		});

		describe('Methods', function () {
			it('should contain 4 methods', function () {
				const methods = testResult.methods;
				const keys = Object.keys(methods);

				expect(keys).to.have.length(4);
			});

			function assertCondition(condition, expected) {
				expect(condition.id).to.be.a('string').and.match(REGEX_UUID);
				expect(condition.comparison).to.equal(expected.comparison);
				expect(condition.arguments).to.include.members(expected.arguments);
				expect(condition.exception).to.equal(expected.exception);
			}

			describe('SimpleMath#Add', function () {
				let method;

				before(function () {
					method = testResult.methods.Add;
				});

				it('should exist with method properties', function () {
					expect(method).to.be.an('object');
					expect(method.id).to.be.a('string').and.match(REGEX_UUID);
					expect(method.visibility).to.equal('Public');
					expect(method.type).to.equal('Integer');
				});

				it('should describe arguments', function () {
					expect(method.arguments).to.be.an('Object')
						.and.have.all.keys(['a', 'b']);
					expect(method.arguments.a).to.equal('Integer');
					expect(method.arguments.b).to.equal('Integer');
				});

				it('should describe preconditions', function () {
					const expectedConditions = [
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['a', 0]
						},
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['b', 0]
						}
					];

					expect(method.preconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.preconditions[index], condition);
					});
				});

				it('should describe postconditions', function () {
					const expectedConditions = [
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['result', 'a']
						}
					];

					expect(method.postconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.postconditions[index], condition);
					});
				});
			});

			describe('SimpleMath#Subtract', function () {
				let method;

				before(function () {
					method = testResult.methods.Subtract;
				});

				it('should exist with method properties', function () {
					expect(method).to.be.an('object');
					expect(method.id).to.be.a('string').and.match(REGEX_UUID);
					expect(method.visibility).to.equal('Public');
					expect(method.type).to.equal('Integer');
				});

				it('should describe arguments', function () {
					expect(method.arguments).to.be.an('Object')
						.and.have.all.keys(['a', 'b']);
					expect(method.arguments.a).to.equal('Integer');
					expect(method.arguments.b).to.equal('Integer');
				});

				it('should describe preconditions', function () {
					const expectedConditions = [
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['a', 0]
						},
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['b', 0]
						},
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['a', 'b']
						}
					];

					expect(method.preconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.preconditions[index], condition);
					});
				});

				it('should describe postconditions', function () {
					const expectedConditions = [
						{
							comparison: 'LessThanOrEqual',
							arguments: ['result', 'a']
						}
					];

					expect(method.postconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.postconditions[index], condition);
					});
				});
			});

			describe('SimpleMath#Divide', function () {
				let method;

				before(function () {
					method = testResult.methods.Divide;
				});

				it('should exist with method properties', function () {
					expect(method).to.be.an('object');
					expect(method.id).to.be.a('string').and.match(REGEX_UUID);
					expect(method.visibility).to.equal('Public');
					expect(method.type).to.equal('Integer');
				});

				it('should describe arguments', function () {
					expect(method.arguments).to.be.an('Object')
						.and.have.all.keys(['a', 'b']);
					expect(method.arguments.a).to.equal('Integer');
					expect(method.arguments.b).to.equal('Integer');
				});

				it('should describe preconditions', function () {
					const expectedConditions = [
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['a', 0]
						},
						{
							comparison: 'GreaterThan',
							arguments: ['b', 0]
						}
					];

					expect(method.preconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.preconditions[index], condition);
					});
				});

				it.skip('should describe postconditions', function () {
					const expectedConditions = [
						{
							comparison: 'Equal',
							arguments: ['result', 'result']
						}
					];

					expect(method.postconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.postconditions[index], condition);
					});
				});
			});

			describe('SimpleMath#SquareRoot', function () {
				let method;

				before(function () {
					method = testResult.methods.SquareRoot;
				});

				it('should exist with method properties', function () {
					expect(method).to.be.an('object');
					expect(method.id).to.be.a('string').and.match(REGEX_UUID);
					expect(method.visibility).to.equal('Public');
					expect(method.type).to.equal('Integer');
				});

				it('should describe arguments', function () {
					expect(method.arguments).to.be.an('Object')
						.and.have.all.keys(['a']);
					expect(method.arguments.a).to.equal('Integer');
				});

				it('should describe preconditions', function () {
					const expectedConditions = [
						{
							comparison: 'GreaterThanOrEqual',
							arguments: ['a', 0]
						}
					];

					expect(method.preconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.preconditions[index], condition);
					});
				});

				it.skip('should describe postconditions', function () {
					const expectedConditions = [
						{
							comparison: 'Equal',
							arguments: ['result', 'result']
						}
					];

					expect(method.postconditions).to.be.instanceOf(Array)
						.and.to.have.length(expectedConditions.length);
					expectedConditions.map((condition, index) => {
						assertCondition(method.postconditions[index], condition);
					});
				});
			});
		});
	}

	describe('SimpleMath.uml', function () {
		const fixture = global.fixtures.FullModels.SimpleMath.uml;

		simpleMathTestSuite(fixture);
	});

	describe('SimpleMath.classdiagram', function () {
		const fixture = global.fixtures.FullModels.SimpleMath.classdiagram;

		simpleMathTestSuite(fixture);
	});
});
