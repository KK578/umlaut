const path = require('path');

const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const chaiFiles = require('chai-files');

chai.use(chaiAsPromised);
chai.use(chaiFiles);

const expect = chai.expect;
const file = chaiFiles.file;
const yeomanHelpers = require('yeoman-test');

const promises = require('../util/promises.js');

const REGEX_UUID = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i;

describe('Component Tests', () => {
	describe('Uml-Parser', () => {
		describe('Visual Studio Parser', () => {
			let testee;

			before(() => {
				testee = require('../uml-parser/parsers/visual-studio/index.js');
			});

			it('should state it cannot parse a non XML string', () => {
				const notXml = 'FooBar';
				const promise = testee.detect(notXml);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result).to.not.be.ok;
				});
			});

			it('should state it cannot parse an arbitrary XML string', () => {
				const notModelXml = '<foo><bar id="bar"></bar</foo>';
				const promise = testee.detect(notModelXml);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result).to.not.be.ok;
				});
			});

			it('should state it can parse if the XML root contains a "modelStoreModel" node', () => {
				const modelXml = '<modelStoreModel></modelStoreModel>';
				const promise = testee.detect(modelXml);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result).to.be.ok;
				});
			});

			it('should state it can parse if the XML root contains a "logicalClassDesignerModel" node', () => {
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

				it('should successfully be detected as parsable', () => {
					return promises.fsReadFile(fixture).then((data) => {
						const promise = testee.detect(data);

						return expect(promise).to.be.fulfilled;
					}).then((result) => {
						expect(result).to.be.ok;
					});
				});

				it('should successfully be parsed', () => {
					return promises.fsReadFile(fixture).then((data) => {
						const promise = testee.parse(data);

						return expect(promise).to.be.fulfilled;
					}).then((result) => {
						expect(result.SimpleMath).to.be.an('object');
						testResult = result.SimpleMath;
					});
				});

				describe('Variables', () => {
					it('should contain a single variable "Nop"', () => {
						const variable = testResult.variables.Nop;

						expect(variable).to.be.an('object');
						expect(variable.id).to.be.a('string').and.match(REGEX_UUID);
						expect(variable.visibility).to.equal('Private');
						expect(variable.type).to.equal('Integer');
					});
				});

				describe('Methods', () => {
					it('should contain 4 methods', () => {
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

					describe('SimpleMath#Add', () => {
						let method;

						before(() => {
							method = testResult.methods.Add;
						});

						it('should exist with method properties', () => {
							expect(method).to.be.an('object');
							expect(method.id).to.be.a('string').and.match(REGEX_UUID);
							expect(method.visibility).to.equal('Public');
							expect(method.type).to.equal('Integer');
						});

						it('should describe arguments', () => {
							expect(method.arguments).to.be.an('Object')
								.and.have.all.keys(['a', 'b']);
							expect(method.arguments.a).to.equal('Integer');
							expect(method.arguments.b).to.equal('Integer');
						});

						it('should describe preconditions', () => {
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

						it('should describe postconditions', () => {
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

					describe('SimpleMath#Subtract', () => {
						let method;

						before(() => {
							method = testResult.methods.Subtract;
						});

						it('should exist with method properties', () => {
							expect(method).to.be.an('object');
							expect(method.id).to.be.a('string').and.match(REGEX_UUID);
							expect(method.visibility).to.equal('Public');
							expect(method.type).to.equal('Integer');
						});

						it('should describe arguments', () => {
							expect(method.arguments).to.be.an('Object')
								.and.have.all.keys(['a', 'b']);
							expect(method.arguments.a).to.equal('Integer');
							expect(method.arguments.b).to.equal('Integer');
						});

						it('should describe preconditions', () => {
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

						it('should describe postconditions', () => {
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

					describe('SimpleMath#Divide', () => {
						let method;

						before(() => {
							method = testResult.methods.Divide;
						});

						it('should exist with method properties', () => {
							expect(method).to.be.an('object');
							expect(method.id).to.be.a('string').and.match(REGEX_UUID);
							expect(method.visibility).to.equal('Public');
							expect(method.type).to.equal('Integer');
						});

						it('should describe arguments', () => {
							expect(method.arguments).to.be.an('Object')
								.and.have.all.keys(['a', 'b']);
							expect(method.arguments.a).to.equal('Integer');
							expect(method.arguments.b).to.equal('Integer');
						});

						it('should describe preconditions', () => {
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

						it.skip('should describe postconditions', () => {
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

					describe('SimpleMath#SquareRoot', () => {
						let method;

						before(() => {
							method = testResult.methods.SquareRoot;
						});

						it('should exist with method properties', () => {
							expect(method).to.be.an('object');
							expect(method.id).to.be.a('string').and.match(REGEX_UUID);
							expect(method.visibility).to.equal('Public');
							expect(method.type).to.equal('Integer');
						});

						it('should describe arguments', () => {
							expect(method.arguments).to.be.an('Object')
								.and.have.all.keys(['a']);
							expect(method.arguments.a).to.equal('Integer');
						});

						it('should describe preconditions', () => {
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

						it.skip('should describe postconditions', () => {
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

			describe('SimpleMath.uml', () => {
				const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

				simpleMathTestSuite(fixture);
			});

			describe('SimpleMath.classdiagram', () => {
				const fixture = path.join(__dirname, './fixtures/SimpleMath/SimpleMath.classdiagram');

				simpleMathTestSuite(fixture);
			});
		});
	});

	describe('Input-Generator', () => {
		let testee;

		describe('SMT-Solver', () => {
			before(() => {
				testee = require('../input-generator/smt-solver/index.js');
			});

			describe('SimpleMath Test Fixture', () => {
				let testResult;

				before(() => {
					const fixture = require(path.join(__dirname, './fixtures/uml/SimpleMath.json'));
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
	});

	describe('Test-Generator', () => {
		describe('JUnit', () => {
			beforeEach(() => {
				const fixture = require(path.join(__dirname, './fixtures/inputs/SimpleMath.json'));

				return yeomanHelpers.run(path.join(__dirname, '../generators/app'))
					.inDir('test/tmp/junit/')
					.withOptions({
						model: JSON.stringify(fixture),
						framework: 'junit'
					});
			});

			it('should make a test suite for SimpleMath', () => {
				expect(file('build/SimpleMathTest.java')).to.exist;
			});

			afterEach(() => {
				// Reset location due to changing from helpers running in specific directory.
				process.chdir('../../../');
			});
		});

		describe('NUnit', () => {
			beforeEach(() => {
				const fixture = require(path.join(__dirname, './fixtures/inputs/SimpleMath.json'));

				return yeomanHelpers.run(path.join(__dirname, '../generators/app'))
					.inDir('test/tmp/nunit/')
					.withOptions({
						model: JSON.stringify(fixture),
						framework: 'nunit'
					});
			});

			it('should make a test suite for SimpleMath', () => {
				expect(file('build/SimpleMathTest.cs')).to.exist;
			});

			afterEach(() => {
				// Reset location due to changing from helpers running in specific directory.
				process.chdir('../../../');
			});
		});
	});
});
