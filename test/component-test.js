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

			describe('SimpleMath Test Fixture', () => {
				let testResult;

				it('should successfully be detected as parsable', () => {
					const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

					return promises.fsReadFile(fixture).then((data) => {
						const promise = testee.detect(data);

						return expect(promise).to.be.fulfilled;
					}).then((result) => {
						expect(result).to.be.ok;
					});
				});

				it('should successfully be parsed', () => {
					const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

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
						expect(variable.visibility).to.equal('private');
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
							expect(method.visibility).to.equal('public');
							expect(method.type).to.equal('Integer');
						});

						it('should describe arguments', () => {
							expect(method.arguments).to.be.instanceOf(Array)
								.and.have.all.keys(['a', 'b']);
							expect(method.arguments.a).to.equal('Integer');
							expect(method.arguments.b).to.equal('Integer');
						});

						it('should describe preconditions', () => {
							expect(method.preconditions).to.be.instanceOf(Array)
								.and.to.have.length(2);

							const condition1 = method.preconditions[0];
							const condition2 = method.preconditions[1];

							assertCondition(condition1, {
								comparison: 'GreaterThanOrEqual',
								arguments: ['a', 0]
							});
							assertCondition(condition2, {
								comparison: 'GreaterThanOrEqual',
								arguments: ['b', 0]
							});
						});

						it('should describe postconditions', () => {
							expect(method.postconditions).to.be.instanceOf(Array)
								.and.to.have.length(1);

							const condition1 = method.preconditions[0];

							assertCondition(condition1, {
								comparison: 'GreaterThanOrEqual',
								arguments: ['result', 'a']
							});
						});
					});
				});
			});
		});
	});

	describe('Input-Ienerator', () => {
		let testee;

		describe('SMT-Solver', () => {
			before(() => {
				testee = require('../input-generator/smt-solver/index.js');
			});

			it('should run against SimpleMath test fixture', () => {
				const fixture = require(path.join(__dirname, './fixtures/test-generator/uml/SimpleMath.json'));
				const promise = testee(fixture);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result.SimpleMath).to.be.an('object');
				});
			});
		});
	});

	describe('Test-Generator', () => {
		describe('JUnit', () => {
			beforeEach(() => {
				return yeomanHelpers.run(path.join(__dirname, '../generators/junit'))
					.inDir('test/tmp/junit/')
					.withArguments([
						// Relative to the above directory.
						'../../fixtures/test-generator/uml/',
						'../../fixtures/test-generator/smt/'
					]);
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
				return yeomanHelpers.run(path.join(__dirname, '../generators/nunit'))
					.inDir('test/tmp/nunit/')
					.withArguments([
						// Relative to the above directory.
						'../../fixtures/test-generator/uml/',
						'../../fixtures/test-generator/smt/'
					]);
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
