# react-searchable-dropdown 1.0.4

## How to install


```
# NPM
npm i the-ultimate-and-the-best-react-searchable-dropdown

#YARN
yarn add the-ultimate-and-the-best-react-searchable-dropdown
```

## Story Book Demo

https://613c0ae26a019e003a9d89ed-izjxtolrre.chromatic.com/

## Component Info

There are MultipleSelector and Selector dropdown component, both are handle long list of choices by using lib react-window (https://github.com/bvaughn/react-window) and using style and component from material-ui (https://material-ui.com/)

## Selector Info

### Selector Special Type

| type name | type | Description |
| --- | --- | --- |
| `Choice` | { label: string; used?: boolean; description?: string; [key: string]: any; } | choice object that we provide to the selector, choice must have label and you can add any arbitary attribute to it so it will return when the choice is selected, description is a string showing on choice tooltip |
| `ChoiceSection` | { choices: Choice[]; sectionName?: string; sectionPrefix?: any; } | contain section name, section prefix and choices of that section |
| `SearchTextFieldProps` | TextFieldProps (from material-ui)| search textfield props type, it is exported from Selector component |
| `SearchTextFieldInputProps` | Partial\<InputProps\> \| Partial\<FilledInputProps\> \| Partial\<OutlinedInputProps\> (all from material-ui)| search textfield input props type, it is exported from Selector component |

### Selector Required Props

| name | type | Description |
| --- | --- | --- |
| `label` | string | string label showing on selector div |
| `popUpKey` | string | key for selector popup element |
| `choiceSections` | ChoiceSection\[\] | key for selector popup element |
| `handleSelect` | ({ value, name }: { value: Choice, name: string }) => void | handle function, trigger when a choice is selected |

### Selector Optional Props

| name | type | Description |
| --- | --- | --- |
| `itemHeight` | number | height of item inside popup (for react-window component) |
| `scrollDivHeight` | number | height of popup scroll div (for react-window component) |
| `style` | CSSProperties | HTML style props for top div component that have every other component inside |
| `selectDivPropsStyle` | CSSProperties |  HTML style props for button component that handle click event |
| `className` | string | className for button component that handle click event |
| `labelPrefix` | string | string that will show on the left side of the selector label |
| `name` | string | name of the selector that will also provide to handleSelect function |
| `placeholder` | string | placeholder will show when label is null, undefined or empty string |
| `id` | string | id for selector that will provide to all inside component |
| `tooltip` | string | string that will show on selector tooltip |
| `topDivClassName` | string | className props for top div component that have every other component inside |
| `popupClassName` | string | selector popup className props |
| `sectionNameClassName` | string | popup section name component className props |
| `itemClassName` | string | item className props |
| `disablePortal` | boolean | for disable popup portal |
| `error` | boolean | if error selector will have red border |
| `disable` | boolean | for disable the selector |
| `disableDropDownArrow` | boolean | for hiding arror |
| `dropDownArrowClassName` | string | arrow component className |
| `dropDownArrowComponent` | React.ReactNode | for custom dropdown arrow |
| `searchTextfieldProps` | SearchTextFieldProps | props object for search textfield |
| `searchTextFieldInputProps` | SearchTextFieldInputProps | input props object for search textfield |


## Multiple Selector Info


### Multiple Selector Special Type

| type name | type | Description |
| --- | --- | --- |
| `Choice` | { label: string; used?: boolean; checked?: boolean; singleChoice?: boolean; id?: string; [key: string]: any; } | choice object that we provide to the selector, choice must have label and you can add any arbitary attribute to it so it will return when the choice is selected, if singleChoice is true handleSelect will trigger when click on this choice |
| `ChoiceSection` | { choices: Choice[]; sectionName?: string; sectionPrefix?: any; } | contain section name, section prefix and choices of that section |
| `SearchTextFieldProps` | TextFieldProps (from material-ui)| search textfield props type, it is exported from Selector component |
| `SearchTextFieldInputProps` | Partial\<InputProps\> \| Partial\<FilledInputProps\> \| Partial\<OutlinedInputProps\> (all from material-ui)| search textfield input props type, it is exported from Selector component |

### Multiple Selector Required Props

| name | type | Description |
| --- | --- | --- |
| `label` | string | string label showing on selector div |
| `popUpKey` | string | key for selector popup element |
| `choiceSections` | ChoiceSection\[\] | key for selector popup element |
| `handleSelect` | ({ value, name }: { value: Choice[], name: string }) => void | handle function, trigger when a sigleChoice choice is click or popup is close |

### Multiple Selector Optional Props

| name | type | Description |
| --- | --- | --- |
| `itemHeight` | number | height of item inside popup (for react-window component) |
| `scrollDivHeight` | number | height of popup scroll div (for react-window component) |
| `style` | CSSProperties | HTML style props for top div component that have every other component inside |
| `selectDivPropsStyle` | CSSProperties |  HTML style props for button component that handle click event |
| `className` | string | className for button component that handle click event |
| `labelPrefix` | string | string that will show on the left side of the selector label |
| `name` | string | name of the selector that will also provide to handleSelect function |
| `placeholder` | string | placeholder will show when label is null, undefined or empty string |
| `id` | string | id for selector that will provide to all inside component |
| `tooltip` | string | string that will show on selector tooltip |
| `topDivClassName` | string | className props for top div component that have every other component inside |
| `popupClassName` | string | selector popup className props |
| `sectionNameClassName` | string | popup section name component className props |
| `itemClassName` | string | item className props |
| `checkedChoices` | Choice[] | lish that contain all check choice, if provide choices that are in checkedChoices will be checked when open popup |
| `error` | boolean | if error selector will have red border |
| `disable` | boolean | for disable the selector |
| `disableDropDownArrow` | boolean | for hiding arror |
| `dropDownArrowClassName` | string | arrow component className |
| `dropDownArrowComponent` | React.ReactNode | for custom dropdown arrow |
| `searchTextfieldProps` | SearchTextFieldProps | props object for search textfield |
| `searchTextFieldInputProps` | SearchTextFieldInputProps | input props object for search textfield |


