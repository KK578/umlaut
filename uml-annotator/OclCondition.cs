using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public OclComparison Comparator { get; set; }
		private List<string> arguments;
		private string exception;
		public string Exception
		{
			get { return exception; }
		}
		private bool isInverted;
		public bool IsInverted
		{
			get { return isInverted; }
		}

		public OclCondition()
		{
			arguments = new List<string>();
			// Add two blank arguments to correspond to left and right arguments.
			arguments.Add("");
			arguments.Add("");
		}

		public OclCondition(string condition)
		{
			string innerCondition = condition;
			if (innerCondition.StartsWith("("))
			{
				innerCondition = innerCondition.Substring(1, innerCondition.Length - 2);
			}

			if (String.IsNullOrWhiteSpace(innerCondition))
			{
				arguments = new List<string>();
				// Add two blank arguments to correspond to left and right arguments.
				arguments.Add("");
				arguments.Add("");

				return;
			}

			string[] items = innerCondition.Split(' ');
			// Ternary ensures inversion syntax is handled correctly here.

			isInverted = items[1] == "not";

			Comparator = FindComparison(isInverted ? items[2] : items[1]);

			arguments = new List<string>();
			// Left hand argument is the first.
			arguments.Add(items[0]);
			// Right hand argument is the last.
			arguments.Add(items[isInverted ? 3 : 2]);

			if (items[items.Length - 1].Contains(":"))
			{
				SetException(items[items.Length - 1].Split(':')[1]);
			}
		}

		public void SetArgument(int index, string argument)
		{
			arguments[index] = argument;
		}

		public string GetArgument(int index)
		{
			return arguments[index];
		}

		public void SetException(string ex)
		{
			exception = ex;
		}

		private OclComparison FindComparison(string comparison)
		{
			// HACK: See MainWindow for explanation.
			List<OclComparison> comparisons = MainWindow.comparisonList;

			foreach (OclComparison c in comparisons)
			{
				if (comparison == c.Symbol)
				{
					return c;
				}
			}

			return null;
		}

		public void SetInverted(bool value)
		{
			if (Comparator.IsInvertable)
			{
				isInverted = value;
			}
		}

		public override string ToString()
		{
			if (String.IsNullOrWhiteSpace(arguments[0]) || String.IsNullOrWhiteSpace(arguments[1]) || Comparator == null)
			{
				return "()";
			}

			string symbol = Comparator.Symbol;
			string comparison = isInverted ? "not " + symbol : symbol;
			string main = String.Format("{0} {1} {2}", arguments[0], comparison, arguments[1]);
			string result;

			if (!String.IsNullOrWhiteSpace(exception))
			{
				string formattedException = String.Format("Exception:{0}", exception);
				result = String.Format("({0} {1})", main, formattedException);
			}
			else
			{
				result = String.Format("({0})", main);
			}

			return result;
		}
	}
}
